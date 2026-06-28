/-
  Compiler.ChainQ2Mixed.Schedule — PARALLEL PPM: syntax + a PAPER-ACCURATE,
  level-stratified commutation certificate for the commuting-measurement scheduling
  optimization, plus a PROOF-CARRYING scheduled product that preserves layer structure.

  The optimizer's freedom is not only WHICH path (Path.lean) but also the SCHEDULE:
  some logical Pauli measurements can be measured SIMULTANEOUSLY (one parallel layer).
  Following 2503.05003 ("Parallel Logical Measurements via Quantum Code Surgery"), the
  set of simultaneously-measurable products is STRATIFIED — and crucially NOT all
  parallel layers are ancilla-free:

    * `directDisjoint`       — "conventional parallelism" (Thm 1): logically DISJOINT
                               support (each logical qubit touched by ≤ 1 measurement).
                               ANCILLA-FREE.
    * `directSameOrId`       — the direct generalization (§6.3 opening): the products
                               have the SAME, or identity, action on every logical
                               qubit (no shared qubit carries two DIFFERENT Paulis).
                               ANCILLA-FREE.  Subsumes `directDisjoint`.
    * `commutingWithAncilla` — "ultimate parallelism" (§6.3): an ARBITRARY pairwise
                               COMMUTING set.  This is NOT ancilla-free — the paper
                               realizes it with TWIST-FREE SURGERY + LOGICAL ANCILLA
                               states (|0⟩, |Y⟩).  We accept it only in this EXPLICIT
                               mode and RECORD the (deferred) ancilla/twist obligation;
                               we do NOT emit the twist-free gadgets.

  So a commuting-but-overlapping layer like `X₀Z₁ ∥ Z₀X₁` is REJECTED by both direct
  (ancilla-free) certificates and accepted only under `commutingWithAncilla` with its
  obligation flagged — it must NOT pass as direct ancilla-free parallel PPM.

  HONEST SCOPE.  This is classical TYPING soundness + the commutation CERTIFICATE.  The
  OPERATIONAL outcome-equivalence of commuting measurements is gated by the certificate
  but not proven (the Mixed IR's PPM channels are `idealChannel`/assumed, CONTRACT §3).
  `CompiledSchedule` PRESERVES the parallel layer boundaries and exposes QStab
  scheduling coordinates (`scheduleCoords` → `QStab.Sched` round/slot); the actual
  MixedInstr→QStab lowering of a multi-measurement schedule is DEFERRED (LS2QStab is a
  one-measurement skeleton — CONTRACT §2).
-/
import Compiler.ChainQ2Mixed.Path
import QStab.Basic

namespace Compiler.ChainQ2Mixed

open Compiler TypeChecker PPM ChainQ.GF2 Logical

/-! ## §D.1. The compositional checker law + whole-program lowering with FRESH
    outcome variables and FRESH gadget ancillas (Bug 5). -/

/-- `checkLogicalExecAux` distributes over `++` — checking `a ++ b` is checking `a`,
    then `b` from the resulting env/state.  (The compositional law a program-level
    soundness fold threads through.) -/
theorem checkLogicalExecAux_append (caps : List Capability) :
    ∀ (a b : LogicalExec) (Γ : TypedEnv) (R : PPMState),
      checkLogicalExecAux caps Γ R (a ++ b) =
        match checkLogicalExecAux caps Γ R a with
        | .ok (Γ', R') => checkLogicalExecAux caps Γ' R' b
        | .error e     => .error e := by
  intro a
  induction a with
  | nil => intro b Γ R; rfl
  | cons i rest ih =>
      intro b Γ R
      simp only [List.cons_append, checkLogicalExecAux]
      cases checkInstr caps Γ R i with
      | ok p => obtain ⟨Γ', R'⟩ := p; exact ih b Γ' R'
      | error e => rfl

/-- Lower a whole program of `(op, realization)` choices, THREADING the env/resources,
    a FRESH outcome-variable counter (`fresh`, advanced by 3 per op — matching
    `compileProgram`'s discipline), and a FRESH ancilla supply (one ancilla per op).
    Concatenates each op's (possibly multi-instruction) lowering.  Threading fresh
    outcome vars + ancillas is LOAD-BEARING: with the checker's SSA freshness guard,
    reusing them across gadget ops would make the program REJECTED. -/
def realizeProgram? (caps : List Capability) :
    List (Compiler.LogicalOp × Realization) → TypedEnv → PPMState → CVar → AncillaSupply →
    Except TypeError (List MixedInstr × TypedEnv × PPMState)
  | [], Γ, R, _, _ => .ok ([], Γ, R)
  | (op, real) :: rest, Γ, R, fresh, sup =>
      match realizeOp? caps sup.alloc.1 fresh (fresh + 1) (fresh + 2) op real Γ R with
      | .ok (instrs, Γ', R') =>
          match realizeProgram? caps rest Γ' R' (fresh + 3) sup.alloc.2 with
          | .ok (rest', Γ'', R'') => .ok (instrs ++ rest', Γ'', R'')
          | .error e             => .error e
      | .error e => .error e

/-- **Whole-program soundness for every choice of realizations** (with fresh
    outcome/ancilla threading).  Folds `realizeOp?_sound` via the append law. -/
theorem realizeProgram?_sound (caps : List Capability) :
    ∀ (prog : List (Compiler.LogicalOp × Realization)) (Γ : TypedEnv) (R : PPMState)
      (fresh : CVar) (sup : AncillaSupply) {instrs : List MixedInstr}
      {Γ' : TypedEnv} {R' : PPMState},
      realizeProgram? caps prog Γ R fresh sup = .ok (instrs, Γ', R') →
      checkLogicalExecAux caps Γ R instrs = .ok (Γ', R') := by
  intro prog
  induction prog with
  | nil =>
      intro Γ R fresh sup instrs Γ' R' h
      simp only [realizeProgram?, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  | cons opr rest ih =>
      intro Γ R fresh sup instrs Γ' R' h
      obtain ⟨op, real⟩ := opr
      simp only [realizeProgram?] at h
      cases h1 : realizeOp? caps sup.alloc.1 fresh (fresh + 1) (fresh + 2) op real Γ R with
      | error e => simp only [h1] at h; exact absurd h (by simp)
      | ok p1 =>
        obtain ⟨instrs1, Γ₁, R₁⟩ := p1
        cases h2 : realizeProgram? caps rest Γ₁ R₁ (fresh + 3) sup.alloc.2 with
        | error e => simp only [h1, h2] at h; exact absurd h (by simp)
        | ok p2 =>
          obtain ⟨instrs2, Γ₂, R₂⟩ := p2
          simp only [h1, h2, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rw [checkLogicalExecAux_append,
            realizeOp?_sound caps sup.alloc.1 fresh (fresh + 1) (fresh + 2) op real Γ R h1]
          exact ih Γ₁ R₁ (fresh + 3) sup.alloc.2 h2

/-! ## §D.2. Parallel PPM layers + the LEVEL-STRATIFIED commutation certificate (Bug 3). -/

/-- The number of logical qubits on which two measurement targets carry ANTICOMMUTING
    letters.  (X, Y, Z are all non-identity, so on a shared qubit the letters
    anticommute iff they differ; `MTarget.wf` makes each qubit appear once.) -/
def antiOverlap (P Q : MTarget) : Nat :=
  (P.filter (fun pp => Q.any (fun qq => decide (qq.1 = pp.1) && decide (pp.2 ≠ qq.2)))).length

/-- The number of logical qubits SHARED by two targets (regardless of letter). -/
def sharedQubits (P Q : MTarget) : Nat :=
  (P.filter (fun pp => Q.any (fun qq => decide (qq.1 = pp.1)))).length

/-- **Logically DISJOINT** support (2503.05003 Def 1.4): no shared logical qubit.
    "Conventional parallelism" — ancilla-free (Thm 1). -/
def mtargetDisjoint (P Q : MTarget) : Bool := sharedQubits P Q == 0

/-- **Same-or-identity** action per logical qubit (2503.05003 §6.3 opening): no shared
    logical qubit carries two DIFFERENT Paulis.  The direct GENERALIZATION — still
    ancilla-free.  Subsumes `mtargetDisjoint`. -/
def mtargetSameOrId (P Q : MTarget) : Bool := antiOverlap P Q == 0

/-- Two products COMMUTE: an EVEN number of anticommuting shared qubits (symplectic
    inner product `0` over GF(2)).  "Ultimate parallelism" (§6.3) — NOT ancilla-free. -/
def mtargetCommute (P Q : MTarget) : Bool := antiOverlap P Q % 2 == 0

/-- A PARALLEL PPM layer: logical Pauli measurements (outcome var + target) claimed
    to be measured SIMULTANEOUSLY. -/
abbrev Layer := List (CVar × MTarget)

/-- A SCHEDULE: a sequence of parallel layers (sequential ∘ parallel). -/
abbrev Schedule := List Layer

/-- The parallelization MODE — which 2503.05003 construction the optimizer is invoking;
    it fixes WHICH commutation certificate the layer must satisfy and whether logical
    ancillas / twist-free surgery are required. -/
inductive ScheduleMode
  | directDisjoint        -- conventional (Thm 1): logically disjoint; ANCILLA-FREE
  | directSameOrId        -- direct generalized (§6.3): same-or-identity per qubit; ANCILLA-FREE
  | commutingWithAncilla  -- ultimate (§6.3): arbitrary commuting; REQUIRES logical ancilla + twist-free surgery (DEFERRED)
  deriving DecidableEq, Repr

/-- Does this mode require (currently deferred) logical-ancilla / twist-free machinery? -/
def ScheduleMode.needsAncilla : ScheduleMode → Bool
  | .commutingWithAncilla => true
  | _                     => false

/-- Check a symmetric relation on all DISTINCT pairs of a layer's targets (each
    unordered pair once — `rel` is checked on `P` against every LATER target). -/
def layerPairwise (rel : MTarget → MTarget → Bool) : Layer → Bool
  | []            => true
  | (_, P) :: rest => rest.all (fun qm => rel P qm.2) && layerPairwise rel rest

/-- **The mode-indexed parallel-layer certificate.**  The optimizer must establish the
    relation appropriate to the construction it claims: disjoint / same-or-identity
    (ancilla-free) or arbitrary-commuting (ancilla-required). -/
def layerCertOk (mode : ScheduleMode) (L : Layer) : Bool :=
  match mode with
  | .directDisjoint       => layerPairwise mtargetDisjoint L
  | .directSameOrId       => layerPairwise mtargetSameOrId L
  | .commutingWithAncilla => layerPairwise mtargetCommute L

/-- Every layer satisfies the mode's certificate. -/
def scheduleCertOk (mode : ScheduleMode) (S : Schedule) : Bool :=
  S.all (layerCertOk mode)

/-! ### Outcome-variable distinctness (Bug 2, schedule side). -/

/-- A Bool no-duplicates check over classical outcome variables. -/
def noDupCVar : List CVar → Bool
  | []      => true
  | x :: xs => ! xs.contains x && noDupCVar xs

/-- A SCHEDULE binds distinct outcome variables across ALL layers (SSA over the whole
    program), and in particular WITHIN each parallel layer (two SIMULTANEOUS
    measurements cannot share a classical result).  This is a DEFENSIVE EARLY check: it
    rejects a duplicate-`CVar` schedule before lowering with a precise message.  It is
    NOT the load-bearing guarantee — the CHECKER is: `checkPPMStmt` rejects a
    measurement binding an already-bound outcome (`TypeError.outcomeReused`), and since
    `compileScheduled?` runs `checkLogicalExecAux` on the flattened lowering, every
    duplicate — same-layer or cross-layer — is caught there regardless of this check.
    (So dropping this guard would not change which schedules are accepted, only which
    error is reported and how early.) -/
def scheduleVarsDistinct (S : Schedule) : Bool :=
  noDupCVar (S.flatMap (fun L => L.map Prod.fst))

/-! ## §D.3. Lowering + the PROOF-CARRYING, structure-preserving `CompiledSchedule`
    (Bug 4). -/

/-- Lower one parallel layer to Mixed instructions (one `.ppm` measurement each).  The
    layer's MEANING is the sequence; the commutation certificate is what makes the
    parallel/any-order reading valid (ancilla-free for the direct modes). -/
def lowerLayer (L : Layer) : List MixedInstr :=
  L.map (fun rP => .ppm (.meas rP.1 rP.2))

/-- A COMPILED schedule that KEEPS the parallel layer boundaries (`layers :
    List (List MixedInstr)`) alongside the proof that its flattened (sequential)
    realization type-checks.  The evidence-carrying analogue of `CompiledMixed` for a
    scheduled program.  `ancillaObligationDeferred` records — honestly — whether the
    chosen mode left a twist-free/logical-ancilla obligation unmet (2503.05003 §6.3). -/
structure CompiledSchedule (caps : List Capability) (Γ₀ : TypedEnv) (R₀ : PPMState) where
  mode    : ScheduleMode
  layers  : List (List MixedInstr)
  envOut  : TypedEnv
  resOut  : PPMState
  /-- the FLATTENED program (the sequential realization of the schedule) type-checks. -/
  typed   : checkLogicalExecAux caps Γ₀ R₀ layers.flatten = .ok (envOut, resOut)
  /-- `true` ⟺ the mode needs (currently DEFERRED) logical ancilla + twist-free surgery. -/
  ancillaObligationDeferred : Bool

/-- **Checked schedule ⟹ checker acceptance** (the defining evidence). -/
theorem CompiledSchedule.checks {caps : List Capability} {Γ₀ : TypedEnv} {R₀ : PPMState}
    (c : CompiledSchedule caps Γ₀ R₀) :
    checkLogicalExecAux caps Γ₀ R₀ c.layers.flatten = .ok (c.envOut, c.resOut) := c.typed

/-- **The public scheduled compiler.**  (1) REQUIRE the mode's parallelization
    certificate (reject a layer that does not parallelize ancilla-free in a `direct`
    mode); (2) REQUIRE distinct outcome variables across the whole schedule; (3) lower
    each layer (preserving boundaries) and run the mixed checker on the flattened
    program — the carried proof IS its acceptance. -/
def compileScheduled? (mode : ScheduleMode) (caps : List Capability) (Γ : TypedEnv)
    (R : PPMState) (S : Schedule) : Except TypeError (CompiledSchedule caps Γ R) :=
  if ! scheduleCertOk mode S then
    .error (.other "ChainQ2Mixed.schedule: a layer violates the chosen mode's parallelization certificate")
  else if ! scheduleVarsDistinct S then
    .error (.other "ChainQ2Mixed.schedule: duplicate outcome variable in a parallel layer / across the schedule")
  else
    match h : checkLogicalExecAux caps Γ R (S.map lowerLayer).flatten with
    | .ok (Γ', R') =>
        .ok { mode := mode, layers := S.map lowerLayer, envOut := Γ', resOut := R',
              typed := h, ancillaObligationDeferred := mode.needsAncilla }
    | .error e => .error e

/-- **Soundness of the scheduled compiler.**  A certified, var-distinct, lowerable
    schedule produces a Mixed program accepted by `checkLogicalExecAux`. -/
theorem compileScheduled?_sound (mode : ScheduleMode) (caps : List Capability) (Γ : TypedEnv)
    (R : PPMState) (S : Schedule) {c : CompiledSchedule caps Γ R}
    (_h : compileScheduled? mode caps Γ R S = .ok c) :
    checkLogicalExecAux caps Γ R c.layers.flatten = .ok (c.envOut, c.resOut) := c.checks

/-! ### QStab scheduling coordinates — the layer structure that SURVIVES the boundary.

    `scheduleCoords` assigns each measurement its `QStab.Sched` coordinate
    (`round` = layer index, `slot` = position within the layer).  This is the
    structure-preserving artifact a future `Schedule → QStab` pass consumes; it shows
    the parallel boundaries map onto QStab scheduling coordinates.  The actual
    MixedInstr→QStab lowering of a multi-measurement schedule is DEFERRED. -/
def scheduleCoords (S : Schedule) : List (CVar × QStab.Sched) :=
  (List.range S.length).flatMap (fun r =>
    match S[r]? with
    | none   => []
    | some L =>
        (List.range L.length).filterMap (fun s =>
          match L[s]? with
          | some (cv, _) => some (cv, ({ round := r, slot := s } : QStab.Sched))
          | none         => none))

/-! ## §D.4. Test fixtures: bare multi-logical environments. -/

/-- A bare `k`-logical block (no stabilizers; `lx[i]`/`lz[i]` are the unit logical
    `X̄ᵢ`/`Z̄ᵢ`).  Valid + complete for any `k` (`k = n − rank ∅`). -/
def bareKBlock (k : Nat) : Block :=
  { n := k, stab := [],
    lx := (List.range k).map (fun i => (List.range (2 * k)).map (fun j => decide (j = i))),
    lz := (List.range k).map (fun i => (List.range (2 * k)).map (fun j => decide (j = k + i))) }

/-- The single-block bare `k`-logical env. -/
def bareKEnv (k : Nat) : TypedEnv :=
  match TypedEnv.ofEnv? { blocks := [bareKBlock k] } with
  | .ok Γ    => Γ
  | .error _ => { blocks := [] }

-- the bare 4-logical block is a valid, complete code:
example : Block.valid (bareKBlock 4) = true := by decide
example : ok? (TypedEnv.ofEnv? { blocks := [bareKBlock 4] }) = true := by decide

/-! ## §D.5. Examples / regression tests for the audited bugs. -/

/-! ### Bug 3: the certificate is LEVEL-STRATIFIED and paper-accurate. -/

-- `X₀Z₁ ∥ Z₀X₁`: COMMUTES but OVERLAPS with DIFFERENT Paulis on each shared qubit.
def overlapLayer : Layer :=
  [(0, [(⟨0, 0⟩, .X), (⟨0, 1⟩, .Z)]), (1, [(⟨0, 0⟩, .Z), (⟨0, 1⟩, .X)])]
-- it is REJECTED by BOTH ancilla-free certificates …
example : layerCertOk .directDisjoint overlapLayer = false := by decide
example : layerCertOk .directSameOrId overlapLayer = false := by decide
-- … and accepted ONLY under the explicit ancilla/twist-free mode (with its obligation):
example : layerCertOk .commutingWithAncilla overlapLayer = true := by decide

-- conventional parallelism: logically DISJOINT support is ancilla-free.
def disjointLayer : Layer := [(0, [(⟨0, 0⟩, .Z)]), (1, [(⟨0, 1⟩, .Z)])]
example : layerCertOk .directDisjoint disjointLayer = true := by decide
example : layerCertOk .directSameOrId disjointLayer = true := by decide

-- direct GENERALIZED: overlap on a shared qubit with the SAME letter (Z on q1) is
-- ancilla-free (`directSameOrId`) but NOT logically disjoint.
def sameLetterLayer : Layer :=
  [(0, [(⟨0, 0⟩, .Z), (⟨0, 1⟩, .Z)]), (1, [(⟨0, 1⟩, .Z), (⟨0, 2⟩, .Z)])]
example : layerCertOk .directDisjoint sameLetterLayer = false := by decide
example : layerCertOk .directSameOrId sameLetterLayer = true := by decide

/-! ### Bug 4: compileScheduled? preserves layer structure + records the obligation. -/

-- a conventional (disjoint) two-layer schedule COMPILES in `directDisjoint` mode:
def freshSched : Schedule :=
  [ [(0, [(⟨0, 0⟩, .Z)]), (1, [(⟨0, 1⟩, .Z)])],
    [(2, [(⟨0, 0⟩, .X)]), (3, [(⟨0, 1⟩, .X)])] ]
example : ok? (compileScheduled? .directDisjoint [] (bareKEnv 4) PPMState.init freshSched) = true := by decide
-- the layer boundaries SURVIVE in the product (2 layers preserved):
example : (match compileScheduled? .directDisjoint [] (bareKEnv 4) PPMState.init freshSched with
           | .ok c => c.layers.length == 2 | .error _ => false) = true := by decide
-- the overlapping commuting layer is REJECTED in a direct mode, ACCEPTED with ancilla mode,
-- and the accepted product RECORDS the deferred ancilla/twist obligation:
example : ok? (compileScheduled? .directSameOrId [] (bareKEnv 4) PPMState.init [overlapLayer]) = false := by decide
example : ok? (compileScheduled? .commutingWithAncilla [] (bareKEnv 4) PPMState.init [overlapLayer]) = true := by decide
example : (match compileScheduled? .commutingWithAncilla [] (bareKEnv 4) PPMState.init [overlapLayer] with
           | .ok c => c.ancillaObligationDeferred | .error _ => false) = true := by decide
-- a DIRECT-mode schedule carries NO ancilla obligation:
example : (match compileScheduled? .directDisjoint [] (bareKEnv 4) PPMState.init freshSched with
           | .ok c => c.ancillaObligationDeferred | .error _ => true) = false := by decide

-- QStab coordinates: the 2-layer schedule maps to rounds {0,1}, slots {0,1} per round.
example : scheduleCoords freshSched =
    [ (0, { round := 0, slot := 0 }), (1, { round := 0, slot := 1 }),
      (2, { round := 1, slot := 0 }), (3, { round := 1, slot := 1 }) ] := by decide

/-! ### Bug 2: outcome-variable SSA, layer + checker side. -/

-- SAME-LAYER duplicate outcome var is rejected by the scheduled compiler:
def dupInLayer : Schedule := [[(0, [(⟨0, 0⟩, .Z)]), (0, [(⟨0, 1⟩, .Z)])]]
example : scheduleVarsDistinct dupInLayer = false := by decide
example : ok? (compileScheduled? .directDisjoint [] (bareKEnv 4) PPMState.init dupInLayer) = false := by decide
-- …and it is ALSO rejected by the checker directly (the load-bearing SSA guarantee),
-- so the defensive `scheduleVarsDistinct` gate is not what makes the verdict correct:
example : ok? (checkLogicalExec [] (bareKEnv 4) (dupInLayer.map lowerLayer).flatten) = false := by decide
-- CROSS-LAYER duplicate outcome var is rejected:
def dupCrossLayer : Schedule := [[(0, [(⟨0, 0⟩, .Z)])], [(0, [(⟨0, 1⟩, .Z)])]]
example : ok? (compileScheduled? .directDisjoint [] (bareKEnv 4) PPMState.init dupCrossLayer) = false := by decide
-- a FRESH multi-layer schedule succeeds (already shown for `freshSched`).
example : scheduleVarsDistinct freshSched = true := by decide

-- CHECKER side (Bug 2): two SEQUENTIAL measurements binding the SAME outcome var FAIL
-- the mixed checker (SSA), while DISTINCT outcome vars succeed:
example : ok? (checkLogicalExec [] (bareKEnv 4)
    [.ppm (.meas 0 [(⟨0, 0⟩, .Z)]), .ppm (.meas 0 [(⟨0, 1⟩, .Z)])]) = false := by decide
example : ok? (checkLogicalExec [] (bareKEnv 4)
    [.ppm (.meas 0 [(⟨0, 0⟩, .Z)]), .ppm (.meas 1 [(⟨0, 1⟩, .Z)])]) = true := by decide

/-! ### Bug 5: `realizeProgram?` threads FRESH outcome vars + ancillas across gadget ops. -/

-- Two CZ gadgets lower to a TYPE-CHECKING program ONLY because `realizeProgram?` hands
-- each op FRESH outcome vars (0,1,2 then 3,4,5) and a FRESH ancilla (⟨0,2⟩ then ⟨0,3⟩).
def twoCZGadgets : List (Compiler.LogicalOp × Realization) :=
  [ (.czGate ⟨0, 0⟩ ⟨0, 1⟩, .direct .ppmGadget),
    (.czGate ⟨0, 0⟩ ⟨0, 1⟩, .direct .ppmGadget) ]
example : ok? (realizeProgram? [] twoCZGadgets (bareKEnv 4) PPMState.init 0 (AncillaSupply.fromQ ⟨0, 2⟩)) = true := by decide
-- CONTRAST: the un-threaded lowering (the OLD bug — same ancilla ⟨0,2⟩ + same vars 0,1,2 for
-- BOTH gadgets) is REJECTED (the second reuses a discarded ancilla / an already-bound var):
example : ok? (checkLogicalExec [] (bareKEnv 4)
    [.ppm (progCZAt ⟨0, 0⟩ ⟨0, 1⟩ ⟨0, 2⟩ 0 1 2), .ppm (progCZAt ⟨0, 0⟩ ⟨0, 1⟩ ⟨0, 2⟩ 0 1 2)]) = false := by decide

end Compiler.ChainQ2Mixed
