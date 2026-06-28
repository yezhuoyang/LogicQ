# TypeChecker/Judgment/Transversal

> Legality checkers for transversal/automorphism logical gates and inter-block transversal CNOT, over binary-symplectic Pauli algebra.

This folder is the transversal-gate judgment of the LogicQ TypeChecker. Given a `TypedEnv` (well-formed code blocks already validated as `Block.valid`), it decides whether an arbitrary symplectic action, a uniform single-qubit transversal gate, or a physical inter-block CNOT incidence is a legal logical operation, and returns the induced action on the declared logical X/Z basis. It sits in the stack after the front-end ChainQ code families produce blocks and before the Compiler Mixed IR consumes verified logical actions on the way to the QStab/QClifford physical target.

## What's here

| Module | Role |
| --- | --- |
| [Transversal.lean](../Transversal.lean) | Aggregator: re-exports `Cert` / `Check` / `CNOT` / `Examples` under `namespace TypeChecker` |
| [Cert.lean](Cert.lean) | Evidence structures `TypedAutomorphism` / `TypedTransversal` (verified map + induced logical action) |
| [Check.lean](Check.lean) | `checkLogicalAutomorphism`, `Internal.transversalMap`, `checkTransversal` |
| [CNOT.lean](CNOT.lean) | Inter-block incidence-checked logical CNOT: specs, `Internal.cnotMap`, `checkTransversalCNOT`, `checkTransversalCNOTBatch` |
| [Examples.lean](Examples.lean) | Worked decidable examples and fixtures (`oneQ`, `bell2`, `rep3`, `hGate`, ...) |

## Key definitions

```lean
structure TypedTransversal where
  block     : BlockId
  gate      : BoolMat        -- the verified 2×2 single-qubit symplectic
  map       : BoolMat        -- its tensor power = the verified 2n×2n action
  inducedLX : BoolMat
  inducedLZ : BoolMat
  deriving Repr
```
([Cert.lean](Cert.lean))

```lean
def checkLogicalAutomorphism (Γ : TypedEnv) (b : BlockId) (M : BoolMat) :
    Except TypeError TypedAutomorphism
```
([Check.lean](Check.lean)) — checks `M` is `2n×2n`, preserves the symplectic form `J`, and maps every stabilizer back into the code.

```lean
def checkTransversal (Γ : TypedEnv) (b : BlockId) (g : BoolMat) :
    Except TypeError TypedTransversal
```
([Check.lean](Check.lean)) — checks a uniform single-qubit `2×2` symplectic `g`, builds its tensor power `Internal.transversalMap blk.n g`, and reuses the automorphism check.

```lean
def checkTransversalCNOT (Gamma : TypedEnv) (spec : TransversalCNOTSpec) :
    Except TypeError TypedTransversalCNOT
```
([CNOT.lean](CNOT.lean)) — enforces physical transversality (row/column weight ≤ 1 incidence), recomputes the joint symplectic action, and checks the induced logical operation is exactly the requested logical CNOT modulo the product stabilizer.

## Example

```lean
-- transversal H on one qubit builds `J 1` and induces X̄ ↦ Z̄:
example : Internal.transversalMap 1 hGate = J 1 := by decide
example : ok? (checkTransversal toneQ 0 hGate) = true := by decide
example : (res? (checkTransversal toneQ 0 hGate)).map (·.inducedLX) = some [[false, true]] := by decide
-- transversal H on two qubits builds `J 2`, legal on the self-dual Bell code:
example : Internal.transversalMap 2 hGate = J 2 := by decide
example : ok? (checkTransversal tbell2 0 hGate) = true := by decide
-- REJECTIONS: transversal H is NOT legal on the non-self-dual repetition code;
example : ok? (checkTransversal trep3 0 hGate) = false := by decide
```

Transversal Hadamard succeeds on a bare qubit and the self-dual `[[2,0,2]]` Bell code but is rejected on the non-self-dual `[[3,1,1]]` repetition code, all discharged `by decide`. Source: [Examples.lean](Examples.lean).

## Status & scope

- **D (`by decide` tests).** Every claim in [Examples.lean](Examples.lean) is an executable decidable check: legality and rejection of transversal H / J automorphisms (`toneQ`, `tbell2`, `trep3`), the bare inter-block logical CNOT (`bareCNOT01`) with its exact induced X/Z images, and physical-transversality rejection of fan-out incidence. These are computational tests of the checkers, not soundness theorems.
- **What the checkers actually decide.** Symplectic-form preservation (`preservesSymp`), stabilizer-into-span (`inSpan`), shape, liveness, and — for CNOT — that the induced logical action equals the requested logical CNOT modulo the joint stabilizer (`Internal.rowsEqualModStab`). These are checks on the *binary-symplectic* (Pauli-frame) representation.
- **A / deferred.** This judgment verifies the symplectic/logical-action legality only. It does NOT prove operational channel correctness, fault tolerance, distance preservation, decoder behaviour, or full operational equivalence of the physical circuit — those obligations live elsewhere and remain deferred per the repo contract. The batched/qLDPC `checkTransversalCNOTBatch` is provided as a generalization but carries no separate soundness theorem here.
- No standalone `theorem` is stated in this folder; the soundness wiring for the judgment lives in the surrounding TypeChecker soundness modules.

## See also

- [../README.md](../README.md) — TypeChecker/Judgment parent overview
- [../../../Compiler/CONTRACT.md](../../../Compiler/CONTRACT.md) — P/D/A/M evidence tiers
- [../../../README.md](../../../README.md) — repository root
