# Compiler/Simulator

> A small exact (unnormalised) state-vector simulator for demos and regression tests over the Mixed IR.

This folder is the executable test harness at the bottom of the LogicQ stack: it runs source-level logical `Gate` circuits and the EMITTED Mixed IR instructions (`Compiler.MixedInstr`) on exact Gaussian-integer state vectors, so the same finite instance can be checked two ways and compared by `by decide`. It is not a typechecker — it consumes what `compile?` produces and validates outcome distributions and source-vs-emitted agreement on the DIRECT (Clifford + Pauli) fragment. Multi-statement PPM gadgets, automorphisms, switches and magic are intentionally NOT executed here (their channel is the deferred ideal-gadget assumption).

## What's here

| Module | Role |
|---|---|
| [Arithmetic.lean](Arithmetic.lean) | Gaussian integers `GInt` (`a + b·i`, Mathlib-free, `DecidableEq`) — the exact amplitude ring |
| [State.lean](State.lean) | `State` = unnormalised `GInt` state vectors + bit helpers (`bit`/`flipBit`/`amp`/`init`) |
| [Gate.lean](Gate.lean) | The simulator gate set `Gate`, `applyGate`/`runGates`, and the measurement read-out `regProb` |
| [Algorithms.lean](Algorithms.lean) | Small Clifford-fragment algorithms (`djConstant`/`djBalanced`/`grover2`/`simon2`) |
| [ExecMixed.lean](ExecMixed.lean) | Layout + source/emitted decoders + the executable interpreter (`simInterp`/`execMixed`) and the M18 alignment theorem |
| [Examples.lean](Examples.lean) | The §5 algorithm-outcome tests, §6 source-vs-emitted comparisons, and the §7 PPM-channel example |

There are no nested subfolders under this directory; the legacy single-file aggregator [../Simulator.lean](../Simulator.lean) sits one level up.

## Key definitions

```lean
/-- Logical gates the simulator understands (a Clifford set + Paulis). -/
inductive Gate
  | H    (i : Nat)
  | S    (i : Nat)
  | X    (i : Nat)
  | Z    (i : Nat)
  | CNOT (c t : Nat)
  | CZ   (c t : Nat)
  deriving Repr, DecidableEq
```

```lean
/-- Apply one gate to the `n`-qubit state (exact, unnormalised). -/
def applyGate (n : Nat) (g : Gate) (s : State) : State
/-- Run a gate list left-to-right. -/
def runGates (n : Nat) (gs : List Gate) (s : State) : State
/-- Total (unnormalised) probability weight of measuring `qubits` to `pat`. -/
def regProb (n : Nat) (qubits : List Nat) (pat : List Bool) (s : State) : Int
```

```lean
/-- The simulator `MixedInterp`: Clifford by its symplectic matrix, a logical Pauli
    APPLIED to the carrier, ideal (identity) measurement back-action. -/
def simInterp (L : Layout) (n : Nat) : MixedInterp State
/-- Run an emitted program left-to-right; `none` if ANY instruction is not executable
    by this fragment-interpreter (no silent drop, unlike `loweredGates`). -/
def execMixed (L : Layout) (n : Nat) : LogicalExec → State → Option State
```

```lean
/-- **ALIGNMENT (the M18 gap closed).**  The executable `.pauli` step produces EXACTLY
    the carrier the operational `Step.pauli` rule yields — both are `simInterp.pauli`. -/
theorem step_pauli_matches_exec (L : Layout) (n : Nat) (caps : List Capability)
    (q : LQubit) (p : PPM.PLetter) (s s' : ExecState State)
    (h : Step (simInterp L n) caps (.pauli q p) s s') :
    execInstr L n (.pauli q p) s.quantum = some s'.quantum
```

## Example

```lean
-- SOURCE vs EMITTED (Task 6): compile `H;S;H` to a proof-carrying mixed program,
-- DECODE the EMITTED transversals, and check the decoded circuit's distribution
-- equals the source circuit's — running the emitted instructions, not source ops.
example : (match compile? .executable { caps := [], anc := ⟨1, 0⟩ } tenvQ hshProg with
           | .ok c => decide (runGates 1 (loweredGates (Layout.flat 4) c.prog) (init 1)
                              = runGates 1 (sourceGates (Layout.flat 4) hshProg) (init 1))
           | .error _ => false) = true := by decide
```

This compiles `H;S;H` through the real `compile?` to a proof-carrying Mixed program, decodes the EMITTED transversal instructions back to gates, and checks by `decide` that the emitted circuit's distribution equals the ideal source circuit's. Source: [Examples.lean](Examples.lean) (§6 tests). Companion checks run Deutsch–Jozsa, two-qubit Grover, and Simon (`n=2`) and confirm their outcome distributions via `regProb … = 0` / `≠ 0` (also `by decide`).

## Status & scope

Honest scope, mirroring [../CONTRACT.md](../CONTRACT.md):

- **D (`by decide` tests).** The algorithm-outcome checks (DJ / Grover / Simon) and the §6 source-vs-emitted equalities are concrete finite instances decided in the kernel. They validate OUTCOME distributions of SOURCE-level `Gate` circuits and exact agreement on the DIRECT transversal + Pauli fragment only.
- **P (proved).** `step_pauli_matches_exec` proves the executable `.pauli` step equals the operational `Step.pauli` carrier update (the M18 alignment) — both reduce to `simInterp.pauli`.
- **A (assumed / ideal channel).** The interpreter's measurement back-action `qinterp.proj` is the identity (ideal). The §7 PPM example exhibits only the classical/frame OUTCOME threading via `PPM.Steps`; the quantum `proj` channel is the deferred part.
- **A / M (deferred).** Multi-statement PPM gadgets, automorphisms, switches and magic are NOT decoded by `loweredGates` and make `execMixed` return `none` (stuck, never silently dropped). The algorithms in [Algorithms.lean](Algorithms.lean) are NOT re-simulated after lowering (a CNOT lowers to a PPM gadget whose channel is deferred). On a multi-block program `execMixed` is the layout-aware per-qubit realization, NOT a literal `execMixed = Step` equality on the transversal fragment.

No `sorry`/`admit`/`native_decide` in this folder. Channel correctness, fault tolerance, distance and decoder claims are out of scope here.

## See also

- Parent: [../README.md](../README.md) — the Compiler layer overview
- Contract / tier legend: [../CONTRACT.md](../CONTRACT.md)
- Repo root: [../../README.md](../../README.md)
