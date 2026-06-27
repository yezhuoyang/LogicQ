/-
  Compiler.Mixed.Lower.Public — the proof-carrying compiled program
  (`CompiledMixed`) and the unified public compiler (`ResourcePool`/`CompileMode`/
  `CompileConfig`/`compile?` + soundness/compilability lemmas), split out of
  Compiler/Mixed/Lower.lean.
-/
import Compiler.Mixed.Lower.Ancilla
import Compiler.Mixed.Lower.LocMap

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical

/-! ## §3·7. Proof-carrying compiled programs — the PUBLIC compiler path. -/

/-- A COMPILED mixed program carrying the proof that it type-checks from the initial
    `(Γ₀, R₀)` — the evidence-carrying analogue of `CompiledPPM` for the whole
    mixed IR.  This is what a successful compilation HANDS to the next stage. -/
structure CompiledMixed (caps : List Capability) (Γ₀ : TypedEnv) (R₀ : PPMState) where
  prog   : LogicalExec
  envOut : TypedEnv
  resOut : PPMState
  typed  : checkLogicalExecAux caps Γ₀ R₀ prog = .ok (envOut, resOut)

/-- **Checked program ⟹ checker acceptance** (the defining evidence). -/
theorem CompiledMixed.checks {caps : List Capability} {Γ₀ : TypedEnv} {R₀ : PPMState}
    (c : CompiledMixed caps Γ₀ R₀) :
    checkLogicalExecAux caps Γ₀ R₀ c.prog = .ok (c.envOut, c.resOut) := c.typed

/-! ### §3·7. The UNIFIED public compiler (M15).

    ONE public entry `compile?` for BOTH modes, sharing ONE operand check
    (`sourceWellFormed`) + the compilability check (lowering).  The M14 executable-path
    OPERAND BUG is fixed: every public
    entry runs the source typechecker FIRST, so a bad logical index (e.g.
    `hGate ⟨b,99⟩`) is REJECTED before any lowering.  `executable` rejects magic
    obligations (`progNoMagic`); `moduloMagic` keeps typed `.magic` obligations.
    Resources are a runtime-checked `ResourcePool` (the M14 checked ancilla pool). -/

/-- The runtime-checked resource pool design (the M14 `AncillaPool`:
    validity/liveness/basis/ownership).  M16: it is NOT YET threaded through
    `compile?` (resource checking beyond operand validity is DEFERRED) — see
    `AncillaPool.alloc` / `alloc_valid` for the checked-allocation primitive, which
    a later pass will thread through `compileProgramLocA`. -/
abbrev ResourcePool := AncillaPool

/-- Which compiler product to emit. -/
inductive CompileMode
  | executable    -- reject magic obligations; every emitted instr has Step semantics
  | moduloMagic   -- accept typed magic obligations (typed, but not executable)
  deriving DecidableEq, Repr

/-- Static compile configuration: capabilities and the ancilla ADDRESS SEED `anc`
    (from which `compileProgramLocA` generates fresh gadget-ancilla addresses).
    M16: resource checking (a threaded `ResourcePool`) is DEFERRED — `anc` is only
    an address seed, not a validity-checked pool. -/
structure CompileConfig where
  caps : List Capability
  anc  : LQubit

/-- **THE PUBLIC COMPILER.**  (1) run the SOURCE WELL-FORMEDNESS check (rejecting
    malformed operands — a clear operand error); (2) lower via the sound
    `compileProgramLocA` (which REJECTS well-formed-but-unimplementable ops, so
    `compile?` checks COMPILABILITY, not merely well-formedness); (3) apply the mode's
    magic policy (`executable` rejects any `.magic`; `moduloMagic` keeps it). -/
def compile? (mode : CompileMode) (cfg : CompileConfig) (Γ : TypedEnv) (ops : List LogicalOp) :
    Except TypeError (CompiledMixed cfg.caps Γ PPMState.init) :=
  if sourceWellFormed cfg.caps Γ PPMState.init ops then
    match h : compileProgramLocA cfg.caps Γ PPMState.init 0 [] (AncillaSupply.fromQ cfg.anc) ops with
    | .ok (prog, Γ', R', _, _) =>
        let c : CompiledMixed cfg.caps Γ PPMState.init :=
          ⟨prog, Γ', R',
            compileProgramLocA_sound cfg.caps ops Γ PPMState.init 0 [] (AncillaSupply.fromQ cfg.anc) h⟩
        match mode with
        | .executable =>
            if progNoMagic prog then .ok c
            else .error (.notImplemented "executable mode rejects magic obligations (T); use moduloMagic")
        | .moduloMagic => .ok c
    | .error e => .error e
  else .error (.other "source program rejected by the source typechecker (bad operand / CNOT control = target / illegal measurement)")

/-- **The public compiler is SOURCE-TYPED**: success (in EITHER mode) implies the
    source program is well-formed.  (So a malformed-operand program is never compiled
    — the M14 bug is closed.) -/
theorem compile?_sourceOk (mode : CompileMode) (cfg : CompileConfig) (Γ : TypedEnv)
    (ops : List LogicalOp) {c : CompiledMixed cfg.caps Γ PPMState.init}
    (h : compile? mode cfg Γ ops = .ok c) :
    sourceWellFormed cfg.caps Γ PPMState.init ops = true := by
  unfold compile? at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- **`sourceCompilable`** — the program has an available implementation in this mode:
    DEFINITIONALLY, `compile?` succeeds.  This is STRICTLY STRONGER than
    `sourceWellFormed`: it additionally requires every op to lower (a legal direct
    transversal / PPM gadget / frame / accepted magic obligation) and the mode's magic
    policy to hold.  `compile?` is exactly the compilability CHECKER. -/
def sourceCompilable (mode : CompileMode) (cfg : CompileConfig) (Γ : TypedEnv)
    (ops : List LogicalOp) : Bool :=
  ok? (compile? mode cfg Γ ops)

/-- Compilable ⇒ well-formed (`compile?` runs the well-formedness check first). -/
theorem sourceCompilable_wellFormed (mode : CompileMode) (cfg : CompileConfig) (Γ : TypedEnv)
    (ops : List LogicalOp) (h : sourceCompilable mode cfg Γ ops = true) :
    sourceWellFormed cfg.caps Γ PPMState.init ops = true := by
  unfold sourceCompilable ok? at h
  split at h
  · exact compile?_sourceOk mode cfg Γ ops ‹_›
  · simp at h

/-! ### §3·7·M22. The SUPPORTED-source-program contract (Task 2). -/

/-- A **SUPPORTED source program**: `compile?` succeeds (DEFINITIONALLY `sourceCompilable`).
    It MEANS: operands are well-formed (`sourceWellFormed`); EVERY op has an available
    lowering (a legal direct transversal / PPM gadget / Pauli `.pauli` / accepted magic
    obligation) — a well-formed-but-unimplementable op makes `compileProgramLocA` `.error`
    and is REJECTED, never silently placed in a placeholder; the required CAPABILITIES are
    present (threaded as `cfg.caps`); and the MODE's magic policy holds (`executable`
    forbids `.magic`).  RESOURCES are IDEAL-ASSUMED: fresh gadget ancillas come from the
    address seed `cfg.anc`, NOT validated against a threaded `ResourcePool` (DEFERRED —
    see `ResourcePool`).  This is DISTINCT from operational EXACTness
    (`Compiler.Demo.exactSupportedOp` / `opBoundary`): a supported program MAY include
    IDEAL-CHANNEL gadget lowerings (`cnotGate`/`czGate`/`measure`) whose carrier channel
    is ASSUMED, not proven. -/
abbrev SupportedSourceProgram (mode : CompileMode) (cfg : CompileConfig)
    (Γ : TypedEnv) (ops : List LogicalOp) : Prop :=
  sourceCompilable mode cfg Γ ops = true

/-- (a) A supported program is source-well-formed (delegates to `sourceCompilable_wellFormed`). -/
theorem SupportedSourceProgram.wellFormed {mode : CompileMode} {cfg : CompileConfig}
    {Γ : TypedEnv} {ops : List LogicalOp} (h : SupportedSourceProgram mode cfg Γ ops) :
    sourceWellFormed cfg.caps Γ PPMState.init ops = true :=
  sourceCompilable_wellFormed mode cfg Γ ops h

/-- (b) A supported program COMPILES to a program that PASSES the mixed checker:
    `compile?` returns a `CompiledMixed` whose carried evidence IS checker acceptance. -/
theorem SupportedSourceProgram.checks {mode : CompileMode} {cfg : CompileConfig}
    {Γ : TypedEnv} {ops : List LogicalOp} (h : SupportedSourceProgram mode cfg Γ ops) :
    ∃ c : CompiledMixed cfg.caps Γ PPMState.init,
      compile? mode cfg Γ ops = .ok c ∧
      checkLogicalExecAux cfg.caps Γ PPMState.init c.prog = .ok (c.envOut, c.resOut) := by
  have h' : ok? (compile? mode cfg Γ ops) = true := h
  cases hc : compile? mode cfg Γ ops with
  | ok c => exact ⟨c, rfl, c.checks⟩
  | error e => rw [hc] at h'; simp [ok?] at h'

end Compiler
