# Compiler/Mixed/Lower

> The source-to-Mixed-IR lowering: compile a straight-line `LogicalOp` source program down to a proof-carrying Mixed IR program.

This folder is the lowering layer of the LogicQ verified-compiler stack. It takes a small logical source DSL (`LogicalOp`: H/S/CNOT/CZ/T/Pauli/measure/transversal-CNOT) and lowers each op through the Mixed-IR type checker (`checkInstr`), so every emitted instruction is type-checked *by construction*. It sits between the TypeChecker legality layer and the Mixed IR (`Compiler/Mixed`): its public entry `compile?` runs the source well-formedness check, lowers via `compileProgramLocA`, and hands the next stage a `CompiledMixed` that carries the proof it passes `checkLogicalExecAux`.

## What's here

| Module | Role |
| --- | --- |
| [Op.lean](Op.lean) | The per-op selector `compileOpR` (`Γ; R ⊢ op ⇝ instr ⊣ Γ'; R'`) + its soundness / completeness / action-soundness theorems |
| [Program.lean](Program.lean) | `compileProgram` (thread Γ, resources, fresh classical vars) + `compileProgram_sound` |
| [LocMap.lean](LocMap.lean) | The logical location / alias map for PPM teleportation gadgets (`LocMap`, `compileProgramLoc`) + soundness |
| [Ancilla.lean](Ancilla.lean) | Ancilla discipline: address supply `AncillaSupply`, proof-carrying `AncillaPool` (`alloc`/`alloc_valid`), `compileProgramLocA` + soundness |
| [ProgramOk.lean](ProgramOk.lean) | The source-program typing judgment (`progOpOk`/`ProgramOk`/`ProgramOkSupported`) + supported-fragment completeness |
| [Public.lean](Public.lean) | The unified public compiler: `CompiledMixed`, `CompileMode`/`CompileConfig`, `compile?`, `SupportedSourceProgram` + soundness lemmas |
| [Examples.lean](Examples.lean) | The `by decide` executable tests (M12–M14) and the `k=2` fixture `tenvQ2` |

## Key definitions

```lean
def compileOpR (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) :
    LogicalOp → Except TypeError (MixedInstr × TypedEnv × PPMState)
```
(from [Op.lean](Op.lean)) — the resource-aware per-op selector.

```lean
theorem compileOp_sound (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) (op : LogicalOp)
    {instr : MixedInstr} {Γ' : TypedEnv} {R' : PPMState}
    (h : compileOpR caps Γ R anc r₁ r₂ r₃ op = .ok (instr, Γ', R')) :
    checkInstr caps Γ R instr = .ok (Γ', R')
```
(from [Op.lean](Op.lean)) — whatever `compileOpR` emits type-checks.

```lean
structure CompiledMixed (caps : List Capability) (Γ₀ : TypedEnv) (R₀ : PPMState) where
  prog   : LogicalExec
  envOut : TypedEnv
  resOut : PPMState
  typed  : checkLogicalExecAux caps Γ₀ R₀ prog = .ok (envOut, resOut)
```
(from [Public.lean](Public.lean)) — the evidence-carrying compiled program.

```lean
def compile? (mode : CompileMode) (cfg : CompileConfig) (Γ : TypedEnv) (ops : List LogicalOp) :
    Except TypeError (CompiledMixed cfg.caps Γ PPMState.init)
```
(from [Public.lean](Public.lean)) — THE public compiler: source check, then lower, then apply the mode's magic policy.

```lean
theorem AncillaPool.alloc_valid (Γ : TypedEnv) (R : PPMState) (basis : AncBasis) (p : AncillaPool)
    {q : LQubit} {p' : AncillaPool} (h : AncillaPool.alloc Γ R basis p = .ok (q, p')) :
    validLQubit Γ q = true ∧ R.dead.contains q = false
```
(from [Ancilla.lean](Ancilla.lean)) — a successfully-allocated ancilla is a valid, non-discarded logical qubit.

## Example

```lean
-- magic policy is the MODE: `executable` rejects `T`, `moduloMagic` accepts it (typed obligation).
example : ok? (compile? .executable  { caps := [], anc := ⟨0, 0⟩ } tenvQ [.tGate ⟨0, 0⟩]) = false := by decide
example : ok? (compile? .moduloMagic { caps := [], anc := ⟨0, 0⟩ } tenvQ [.tGate ⟨0, 0⟩]) = true := by decide
-- both modes reject an INVALID `T` operand (source typecheck fires before the magic policy):
example : ok? (compile? .moduloMagic { caps := [], anc := ⟨0, 0⟩ } tenvQ [.tGate ⟨0, 99⟩]) = false := by decide
-- a valid H/S program compiles in executable mode:
example : ok? (compile? .executable { caps := [], anc := ⟨0, 0⟩ } tenvQ [.hGate ⟨0, 0⟩, .sGate ⟨0, 0⟩]) = true := by decide
```

These `by decide` tests (from [Examples.lean](Examples.lean)) exercise `compile?`: the mode is the magic policy (`executable` rejects `T`, `moduloMagic` keeps the typed `.magic` obligation), a bad operand is rejected by the source typecheck before any lowering, and a direct H/S program compiles.

## Status & scope

Per the contract tiers in [../../CONTRACT.md](../../CONTRACT.md) (P proved theorem, D `by decide` test, A documented assumption, M missing/planned):

- **Proved (P).** `compileOp_sound`, `compileProgram_sound`, `compileProgramLoc_sound`, `compileProgramLocA_sound`, and `AncillaPool.alloc_valid` are real theorems: a compiled program is accepted by the Mixed checker, and a pool allocation yields a valid/live qubit. `compile?_sourceOk` / `sourceCompilable_wellFormed` / `SupportedSourceProgram.checks` establish that a successful `compile?` is source-well-formed and its carried evidence is checker acceptance. `ProgramOkSupported_compiles` proves the direct transversal-H/S fragment always compiles. These are checker-soundness results (typically `propext`-clean), NOT axiom-free.
- **Tested (D).** The `example ... := by decide` cases in [Examples.lean](Examples.lean), [LocMap.lean](LocMap.lean), [ProgramOk.lean](ProgramOk.lean) (operand rejection, ancilla freshness/distinctness, the checked-pool discipline, addressability of `hGate`/`sGate` only on a `k=1` block).
- **Assumed / deferred (A / M).** Soundness is about *type-checking*, NOT channel correctness or fault tolerance. The H/S/CNOT/CZ PPM teleportation gadgets are IDEAL-CHANNEL (carrier channel assumed, not proven) — a `SupportedSourceProgram` may include them. `T` (`.tGate`) lowers to a TYPED but DEFERRED `.magic` obligation with NO `Step` semantics (MagicQ unwired); the `executable` mode rejects it. RESOURCE checking is DEFERRED: `compile?` threads only the address SEED `cfg.anc` (via `AncillaSupply`), and the proof-carrying `ResourcePool`/`AncillaPool` is NOT yet threaded through `compileProgramLocA` (see the `ResourcePool` and `CompileConfig` docstrings in [Public.lean](Public.lean)). Operational EXACTness of gadget lowerings is distinct from this layer's source-typing guarantee.

## See also

- [../README.md](../README.md) — Compiler/Mixed (the Mixed IR target this layer lowers into)
- [../../CONTRACT.md](../../CONTRACT.md) — the proof-obligation tiers (P / D / A / M)
- [../../README.md](../../README.md) — the Compiler stack overview
