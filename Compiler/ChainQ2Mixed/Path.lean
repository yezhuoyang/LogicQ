/-
  Compiler.ChainQ2Mixed.Path — the PATH choice as a first-class, non-deterministic
  (schedulable) parameter, with FIXED deterministic rules per path.

  The Mixed IR already expresses all three realization paths; here we make the
  CHOICE explicit (CompCert/MLIR style): `compileOpWith (choice) op` emits exactly
  ONE candidate `MixedInstr` for the (op, path) pair via `candidate?`, then routes
  it through the existing `checkInstr` (the unconditional legality predicate).  So:

    * the per-path lowering is DETERMINISTIC (`candidate?` is a function);
    * the choice is NON-DETERMINISTIC (`PathChoice` is duplicable compile-time
      metadata — never threaded into the linear resource state);
    * SOUNDNESS holds for EVERY choice (`compileOpWith_sound`), because whatever is
      emitted is exactly what `checkInstr` accepted — a single proof covering all
      paths and all ops.

  This file does the SINGLE-instruction paths (transversal / PPM gadget / Pauli
  frame / transversal-CNOT / magic).  The code-switch path (`switch` + realize in
  the target code) is `Schedule.lean`/`M-C`; scheduling/parallel layers are `M-D`.
  Scope: classical typing soundness; the gadget-channel/FT boundary is inherited
  unchanged from the Mixed IR (see CONTRACT §3 — cnot/cz/multi-H/S are idealChannel).
-/
import Compiler.ChainQ2Mixed.Source

namespace Compiler.ChainQ2Mixed

open Compiler TypeChecker PPM ChainQ.GF2 Logical

/-- The realization path chosen for one logical op (single-instruction paths).
    The same op may allow more than one path — the CHOICE is the optimizer's free
    variable; the lowering of each path is fixed. -/
inductive PathChoice
  | transversalGate     -- a code-automorphism transversal Clifford (`.transversal b g`)
  | ppmGadget           -- a Pauli-product-measurement teleportation gadget (`.ppm …`)
  | pauliFrame          -- a logical Pauli applied to the carrier (`.pauli q p`)
  | transversalCNOTPath -- an incidence-checked inter-block logical CNOT (`.transversalCNOT`)
  | magicObligation     -- a deferred, typed magic-state obligation (`.magic`, e.g. T)
  deriving DecidableEq, Repr

/-- **The fixed per-path lowering rules.**  For a `(path, op)` pair that the path can
    realize, returns the single candidate `MixedInstr`; `none` if the path does not
    apply to that op.  This is the deterministic core; the non-determinism is the
    choice of `PathChoice`.

    SEMANTIC GUARD (matches `Compiler.compileOpR`): a single-LOGICAL gate `hGate q`/
    `sGate q` is realized as a DIRECT block-wide transversal ONLY when `q`'s block is
    single-logical (`singleLogicalBlock Γ q.blk`), where the block-wide action
    coincides with the per-qubit gate.  On a MULTI-logical block, `LogicalOp.srcAction`
    is `none` (a per-qubit gate has no block-wide action), so the transversal path does
    NOT apply — the op must go through a PPM gadget (`.ppmGadget`) or be requested
    explicitly as the block-wide `blockTransversal`.  `blockTransversal b g` is the
    explicit block-wide operation and is unguarded. -/
def candidate? (choice : PathChoice) (Γ : TypedEnv) (op : Compiler.LogicalOp)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) : Option MixedInstr :=
  match choice, op with
  | .transversalGate, .hGate q             =>
      if singleLogicalBlock Γ q.blk then some (.transversal q.blk hGate2x2) else none
  | .transversalGate, .sGate q             =>
      if singleLogicalBlock Γ q.blk then some (.transversal q.blk sGate2x2) else none
  | .transversalGate, .blockTransversal b g => some (.transversal b g)
  | .ppmGadget,       .hGate q             => some (.ppm (progHAt q anc r₁ r₂))
  | .ppmGadget,       .sGate q             => some (.ppm (progSAt q anc r₁ r₂))
  | .ppmGadget,       .cnotGate c t        => some (.ppm (progCNOTAt c t anc r₁ r₂ r₃))
  | .ppmGadget,       .czGate c t          => some (.ppm (progCZAt c t anc r₁ r₂ r₃))
  | .ppmGadget,       .measure r P         => some (.ppm (.meas r P))
  | .pauliFrame,      .xGate q             => some (.pauli q .X)
  | .pauliFrame,      .zGate q             => some (.pauli q .Z)
  | .transversalCNOTPath, .transversalLogicalCNOT c t inc =>
      some (.transversalCNOT { control := c, target := t, incidence := inc })
  | .magicObligation, .tGate q             => some (.magic { kind := .tGate, target := q })
  | _, _ => none

/-- **The path-parameterized lowering.**  Emit the chosen path's candidate and check
    it; the result is type-checked BY CONSTRUCTION.  The current hard-coded selector
    `compileOpR` is the special case of folding a default `Strategy` over the ops. -/
def compileOpWith (choice : PathChoice) (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) (op : Compiler.LogicalOp) :
    Except TypeError (MixedInstr × TypedEnv × PPMState) :=
  match candidate? choice Γ op anc r₁ r₂ r₃ with
  | none => .error (.notImplemented "ChainQ2Mixed: chosen path does not realize this op")
  | some cand =>
    match checkInstr caps Γ R cand with
    | .ok (Γ', R') => .ok (cand, Γ', R')
    | .error e     => .error e

/-- **Soundness for EVERY path choice.**  Whatever instruction `compileOpWith`
    emits — under ANY `PathChoice` — type-checks under the same environment and
    resource state.  One proof for all paths: the emitted instr is exactly the
    candidate that `checkInstr` accepted. -/
theorem compileOpWith_sound (choice : PathChoice) (caps : List Capability) (Γ : TypedEnv)
    (R : PPMState) (anc : LQubit) (r₁ r₂ r₃ : CVar) (op : Compiler.LogicalOp)
    {instr : MixedInstr} {Γ' : TypedEnv} {R' : PPMState}
    (h : compileOpWith choice caps Γ R anc r₁ r₂ r₃ op = .ok (instr, Γ', R')) :
    checkInstr caps Γ R instr = .ok (Γ', R') := by
  unfold compileOpWith at h
  cases hcand : candidate? choice Γ op anc r₁ r₂ r₃ with
  | none => simp [hcand] at h
  | some cand =>
    cases hck : checkInstr caps Γ R cand with
    | error e => simp [hcand, hck] at h
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hcand, hck, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact hck

/-! ## §B. Examples: the same op, multiple paths; cap-free realizations type-check. -/

/-- A single bare logical qubit (k=1) env, reused from the Source examples. -/
def bareEnv : TypedEnv :=
  match elabProgram? bareProg with
  | .ok (Γ, _) => Γ
  | .error _   => { blocks := [] }

-- On a single-logical block, transversal `H`/`S` realize CAP-FREE (code automorphism):
example : ok? (compileOpWith .transversalGate [] bareEnv PPMState.init ⟨1, 0⟩ 0 1 2 (.hGate ⟨0, 0⟩)) = true := by decide
example : ok? (compileOpWith .transversalGate [] bareEnv PPMState.init ⟨1, 0⟩ 0 1 2 (.sGate ⟨0, 0⟩)) = true := by decide
-- A logical Pauli and a (deferred) magic T realize via their paths, cap-free:
example : ok? (compileOpWith .pauliFrame [] bareEnv PPMState.init ⟨1, 0⟩ 0 1 2 (.xGate ⟨0, 0⟩)) = true := by decide
example : ok? (compileOpWith .pauliFrame [] bareEnv PPMState.init ⟨1, 0⟩ 0 1 2 (.zGate ⟨0, 0⟩)) = true := by decide
example : ok? (compileOpWith .magicObligation [] bareEnv PPMState.init ⟨1, 0⟩ 0 1 2 (.tGate ⟨0, 0⟩)) = true := by decide

-- NON-DETERMINISM is REAL: a path that does not realize the op is rejected
-- (transversalGate cannot realize a CNOT; ppmGadget cannot realize a T):
example : ok? (compileOpWith .transversalGate [] bareEnv PPMState.init ⟨1, 0⟩ 0 1 2 (.cnotGate ⟨0, 0⟩ ⟨0, 0⟩)) = false := by decide
example : ok? (compileOpWith .magicObligation [] bareEnv PPMState.init ⟨1, 0⟩ 0 1 2 (.hGate ⟨0, 0⟩)) = false := by decide

/-- A two-logical block `two_logicals` (`left`,`right`), reused from the Source examples. -/
def twoLogicalEnv : TypedEnv :=
  match elabProgram? twoProg with
  | .ok (Γ, _) => Γ
  | .error _   => { blocks := [] }

-- BUG-1 REGRESSION (semantic guard): the DIRECT transversal path is REJECTED for a
-- per-qubit `hGate`/`sGate` on a MULTI-logical block — emitting a block-wide
-- transversal there would NOT realize the single-logical `srcAction` (which is `none`).
-- The op must instead use a PPM gadget or the explicit `blockTransversal`.
example : ok? (compileOpWith .transversalGate [] twoLogicalEnv PPMState.init ⟨2, 0⟩ 0 1 2 (.hGate ⟨0, 1⟩)) = false := by decide
example : ok? (compileOpWith .transversalGate [] twoLogicalEnv PPMState.init ⟨2, 0⟩ 0 1 2 (.hGate ⟨0, 0⟩)) = false := by decide
example : ok? (compileOpWith .transversalGate [] twoLogicalEnv PPMState.init ⟨2, 0⟩ 0 1 2 (.sGate ⟨0, 1⟩)) = false := by decide
-- the EXPLICIT block-wide transversal is still accepted (it is honestly block-wide):
example : ok? (compileOpWith .transversalGate [] twoLogicalEnv PPMState.init ⟨2, 0⟩ 0 1 2 (.blockTransversal 0 hGate2x2)) = true := by decide
-- and direct transversal on a SINGLE-logical block is unaffected (still accepted):
example : ok? (compileOpWith .transversalGate [] bareEnv PPMState.init ⟨1, 0⟩ 0 1 2 (.hGate ⟨0, 0⟩)) = true := by decide

/-! ## §C. The code-switch path: `codeSwitchThen` (the third realization).

    A `Realization` is either a single-instruction `PathChoice`, or a CODE SWITCH of a
    block to a target code `D` (via a checked `SwitchCert`) FOLLOWED BY a realization
    in `D` — this is "code-switch first to unlock a gate the source code lacks".  It
    lowers to a LIST of instructions (`switch :: …`), each type-checked by construction
    against the threaded env.  HONEST SCOPE: the existing `checkSwitch` accepts a
    same-arity TRANSPARENT logical coercion (`kC = kD`, `f` preserves stabilizers and
    X̄/Z̄ mod the target stabilizers); a genuine dimension-jump switch (changing `n`)
    needs bridging `Compiler.CodeSwitch` to `SwitchCert` and is future work. -/

inductive Realization
  | direct         (choice : PathChoice)
  | codeSwitchThen (b : Nat) (D : Block) (cert : SwitchCert) (then_ : Realization)
  deriving Repr

/-- Lower one op via a (possibly multi-instruction) realization; type-checked by
    construction against the THREADED env/resource state. -/
def realizeOp? (caps : List Capability) (anc : LQubit) (r₁ r₂ r₃ : CVar) (op : Compiler.LogicalOp) :
    Realization → TypedEnv → PPMState → Except TypeError (List MixedInstr × TypedEnv × PPMState)
  | .direct choice, Γ, R =>
      match compileOpWith choice caps Γ R anc r₁ r₂ r₃ op with
      | .ok (instr, Γ', R') => .ok ([instr], Γ', R')
      | .error e            => .error e
  | .codeSwitchThen b D cert inner, Γ, R =>
      match checkInstr caps Γ R (.switch b D cert) with
      | .ok (Γ', R') =>
          match realizeOp? caps anc r₁ r₂ r₃ op inner Γ' R' with
          | .ok (rest, Γ'', R'') => .ok (.switch b D cert :: rest, Γ'', R'')
          | .error e             => .error e
      | .error e => .error e

/-- **Soundness for EVERY realization (incl. the code-switch path).**  The whole
    emitted instruction list type-checks under `checkLogicalExecAux` — by induction on
    the realization, reusing `compileOpWith_sound` for the leaf and the switch's own
    `checkInstr` evidence for the code-switch step. -/
theorem realizeOp?_sound (caps : List Capability) (anc : LQubit) (r₁ r₂ r₃ : CVar)
    (op : Compiler.LogicalOp) :
    ∀ (real : Realization) (Γ : TypedEnv) (R : PPMState) {instrs : List MixedInstr}
      {Γ' : TypedEnv} {R' : PPMState},
      realizeOp? caps anc r₁ r₂ r₃ op real Γ R = .ok (instrs, Γ', R') →
      checkLogicalExecAux caps Γ R instrs = .ok (Γ', R') := by
  intro real
  induction real with
  | direct choice =>
      intro Γ R instrs Γ' R' h
      simp only [realizeOp?] at h
      cases hc : compileOpWith choice caps Γ R anc r₁ r₂ r₃ op with
      | error e => simp [hc] at h
      | ok p =>
        obtain ⟨instr, Γ₀, R₀⟩ := p
        simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hck := compileOpWith_sound choice caps Γ R anc r₁ r₂ r₃ op hc
        simp [checkLogicalExecAux, hck]
  | codeSwitchThen b D cert inner ih =>
      intro Γ R instrs Γ' R' h
      simp only [realizeOp?] at h
      cases hsw : checkInstr caps Γ R (.switch b D cert) with
      | error e => simp [hsw] at h
      | ok p =>
        obtain ⟨Γ₁, R₁⟩ := p
        cases hrec : realizeOp? caps anc r₁ r₂ r₃ op inner Γ₁ R₁ with
        | error e => simp [hsw, hrec] at h
        | ok q =>
          obtain ⟨rest, Γ₂, R₂⟩ := q
          simp only [hsw, hrec, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hrest := ih Γ₁ R₁ hrec
          simp [checkLogicalExecAux, hsw, hrest]

/-- A bare logical block (the target of a transparent self-coercion). -/
def bareBlock : Block :=
  { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]], live := true, own := .owned }

-- The code-switch path type-checks: a transparent same-arity switch (here the
-- identity self-coercion on a bare qubit) FOLLOWED BY a logical Pauli in the target.
-- (Demonstrates the third path + the multi-instruction lowering; the switch is the
-- supported transparent class — a genuine dimension jump is future work.)
example :
    ok? (realizeOp? [] ⟨1, 0⟩ 0 1 2 (.xGate ⟨0, 0⟩)
          (.codeSwitchThen 0 bareBlock { kind := .teleport, f := identMat 2 } (.direct .pauliFrame))
          bareEnv PPMState.init) = true := by decide
-- the single-instruction realization also works through the list-returning lowering:
example :
    ok? (realizeOp? [] ⟨1, 0⟩ 0 1 2 (.hGate ⟨0, 0⟩) (.direct .transversalGate) bareEnv PPMState.init) = true := by decide

end Compiler.ChainQ2Mixed
