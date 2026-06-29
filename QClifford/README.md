# QClifford

> The final physical Clifford target IR (level `L_QClifford`).

`QClifford` is the executable artifact at the bottom of the LogicQ stack: a circuit of
**physical** Clifford gates, state preparations, computational (`Z`-basis) measurements,
classical parity assignments, and classically-conditioned Pauli corrections — what a
surface-code device actually runs. It sits below `QStab` as the final lowering target,
reached after the front-end ChainQ code families pass TypeChecker legality and are lowered
through the Compiler Mixed IR. The syntax is pure, Mathlib-free data; the operational
semantics is parametric in a physical `Host`, so the same circuit can be run against a
stabilizer tableau or a density-matrix backend.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Umbrella: imports `Syntax` and `Semantics` for `import QClifford.Basic`. |
| [Syntax.lean](Syntax.lean) | `Gate` / `Circuit` AST, gate predicates, and honest resource counters (`width`, `gateCount`, `twoQubitCount`, `measCount`, `parityCount`). |
| [Semantics.lean](Semantics.lean) | Parametric `Host`, classical `Store`, `applyPauli`, the `run` interpreter, and the `run_append` composition theorem. |

## Key definitions

```lean
/-- A physical Clifford+measurement gate. -/
inductive Gate
  | prepZero (q : PQubit)
  | prepPlus (q : PQubit)
  | H       (q : PQubit)
  | S       (q : PQubit)
  | X       (q : PQubit)
  | Z       (q : PQubit)
  | CNOT    (c t : PQubit)
  | CZ      (a b : PQubit)
  | meas    (q : PQubit) (r : CBit)              -- `Meas q -> r`
  | parity  (r : CBit) (srcs : List CBit)        -- `r := xor srcs`
  | ifPauli (r : CBit) (p : Pauli) (q : PQubit)  -- `If r then P q`
  deriving DecidableEq, Repr, Inhabited
```

```lean
/-- A physical execution host: the Clifford gate actions and a `Z`-measurement. -/
structure Host (St : Type) where
  prepZero  : PQubit → St → St
  ...
  measureZ  : PQubit → St → Bool × St
```

```lean
/-- Run a circuit, threading the physical state and the classical store. -/
def run {St : Type} (Ho : Host St) : Circuit → St → Store → St × Store
```

```lean
/-- **Sequential composition.**  Running `c₁ ++ c₂` is running `c₂` from the
    state/store produced by `c₁` — the composition law the end-to-end
    correctness proof threads through the target. -/
theorem run_append {St : Type} (Ho : Host St) (c₁ c₂ : Circuit) (st : St) (σ : Store) :
    run Ho (c₁ ++ c₂) st σ
      = run Ho c₂ (run Ho c₁ st σ).1 (run Ho c₁ st σ).2
```

## Example

```lean
/-- A `CNOT(c,t)` realized from a `CZ`: `H t; CZ c t; H t`. -/
def cnotFromCZ (c t : PQubit) : Circuit := [.H t, .CZ c t, .H t]

-- cnotFromCZ 0 1 is the concrete circuit (a value of type `Circuit = List Gate`):
[ .H 1, .CZ 0 1, .H 1 ]      -- a CNOT(0,1) decomposed into a CZ conjugated by Hadamards
-- gateCount      = 3   (three gates)
-- twoQubitCount  = 1   (exactly the .CZ)
-- width          = 2   (qubits 0 and 1 touched)
```

A `CNOT` decomposed into a `CZ` conjugated by Hadamards. The concrete circuit value carries
the resource readouts directly: 3 gates, exactly 1 two-qubit gate, width 2.
Source: [Syntax.lean](Syntax.lean) (lines 90–95).

## Status & scope

- **P (proved theorem).** `run_append` is a `propext`-clean composition law (`run Ho (c₁ ++ c₂)` factors through `run Ho c₁` then `run Ho c₂`), proved by induction over `c₁` for **any** host `St`. It is the control-flow law the end-to-end correctness proof threads through the target. It is not "axiom-free" (it rests on standard propositional extensionality).
- **D (`by decide` tests).** The `cnotFromCZ` resource-counter `example`s in `Syntax.lean` are decidable checks on a concrete circuit, not general lemmas.
- **A (documented assumption).** The state `St` and `Host` actions are **parametric / deferred**: `Host` is an abstract interface (`prepZero`, `applyH`, `measureZ`, …) with **no** concrete stabilizer-tableau or density-matrix instance supplied here. Any claim that a given host *implements* Clifford physics is an external/ideal-channel assumption, not proved in this folder.
- **M (missing/planned).** This layer has resource counters and operational semantics, **not a full verifier**: there is no type-checking judgment, no channel-correctness / fault-tolerance / distance / decoder claim, and no operational-equivalence-with-`QStab` theorem in this folder. Those obligations live (or remain deferred) elsewhere in the stack.

## See also

- [../README.md](../README.md) — repository / stack overview.
- [../QStab/README.md](../QStab/README.md) — the stabilizer layer that lowers into this physical target.
- [../Compiler/CONTRACT.md](../Compiler/CONTRACT.md) — the P/D/A/M proof-tiering contract referenced above.
