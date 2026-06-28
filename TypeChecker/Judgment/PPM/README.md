# TypeChecker/Judgment/PPM

> Proof-carrying capability matcher for a SINGLE logical Pauli product measurement (PPM).

This folder holds `checkPPM`, the legality judgment for one logical Pauli-product measurement over a typed
ChainQ environment. It sits in the TypeChecker legality layer: front-end ChainQ code families produce blocks,
this judgment decides whether a requested logical measurement is implementable either natively on one code or
via an installed code-switching / lattice-surgery `Capability`, emitting a `TypedPPM` certificate that the
Mixed-IR compiler and QStab/QClifford physical target can later consume. The whole-program sequencing of these
single measurements lives one level up in [PPMProgram](../PPMProgram/README.md).

## What's here

| Module | Role |
|---|---|
| [Check.lean](Check.lean) | `checkPPM` / `checkPPMFromEnv`: the matcher, native-vs-capability dispatch, and the merged-code certificate checks. |
| [Certificate.lean](Certificate.lean) | `TypedPPM`, the evidence structure returned on success. |
| [Lift.lean](Lift.lean) | Block-diagonal lifting into the merged symplectic space and the named merged-code certificate components (`liftedStabOf`, `mergedStabOf`, `targetPOf`). |
| [Examples.lean](Examples.lean) | Worked `by decide` examples over a bare qubit and the `[[3,1,1]]` repetition code. |

## Key definitions

```lean
structure TypedPPM where
  target      : PPM.MTarget
  kind        : CapKind
  mergedN     : Nat
  obligations : List String
  deriving Repr
```

```lean
def checkPPM (Γ : TypedEnv) (caps : List Capability) (P : PPM.MTarget) :
    Except TypeError TypedPPM
```

```lean
def checkPPMFromEnv (Γ : Env) (caps : List Capability) (P : PPM.MTarget) :
    Except TypeError TypedPPM
```

```lean
def ppmObligations : CapKind → List String
```

```lean
-- (Lift.lean) the named merged-code certificate components
def mergedStabOf (bos : List (BlockId × Block × Nat)) (mergedN : Nat) (connStab : BoolMat) : BoolMat
def targetPOf    (bos : List (BlockId × Block × Nat)) (mergedN : Nat) (P : PPM.MTarget) : BoolVec
```

`checkPPM` rejects an empty target (`emptyMeasurement`), a repeated logical qubit or a non-native (>2 factor)
target (`nonNativeMeasurement`), and an out-of-range logical index (`badLogicalIndex`). A weight-1/2 single-block
target is admitted natively; otherwise it must match an installed `Capability` on the touched blocks whose merge
passes four certificate checks: the merged stabilizers pairwise commute, the merge preserves the data codes, and
the lifted target Pauli is in the span of the merged group.

## Example

```lean
-- single-block logical measurement is native:
example : ok? (checkPPM tenvQ [] [(⟨0, 0⟩, PPM.PLetter.Z)]) = true := by decide
-- DRIVING EXAMPLE: cross-code joint PPM with NO capability is rejected …
example : ok? (checkPPM tenvQR [] zzTarget) = false := by decide
-- … and ADMITTED only with a valid adapter capability …
example : ok? (checkPPM tenvQR [zzCap] zzTarget) = true := by decide
-- … but a degenerate capability (no connection) fails the merged-code certificate.
example : ok? (checkPPM tenvQR [{ zzCap with connStab := [] }] zzTarget) = false := by decide
```

A joint `Z̄ ⊗ Z̄` measurement across a bare qubit and the `[[3,1,1]]` repetition code is rejected with no
capability, admitted only when an adapter capability supplies a valid merge, and rejected again when that
capability has no connection stabilizer. Source: [Examples.lean](Examples.lean).

## Status & scope

These are `by decide` executable tests (tier **D**) confirming that `checkPPM` accepts / rejects the right
targets; the entire example set in [Examples.lean](Examples.lean) is `by decide`-closed. The certificate checks
in [Check.lean](Check.lean) — merged-code commutation, data-code preservation, and target-in-span — are
genuine, concretely-decidable predicates over the lifted symplectic space.

What is NOT claimed here: success of `checkPPM` is evidence that the requested measurement is *structurally*
realizable by a native or capability-backed merge. The physical fault-tolerance content is carried as explicit
DEFERRED obligations (tier **A**/**M**) in the `obligations` field via `ppmObligations` — e.g. merged-code
distance, fault distance `R ≥ d`, decoder for the merged syndrome, relative expansion `β_d ≥ 1`, Cheeger bound,
and schedule feasibility. No channel-correctness, distance, or decoder claim is proved in this folder; those
remain obligations faithful to the source papers. Operational/program-level soundness is stated and proved one
level up (see [PPMProgram/Soundness.lean](../PPMProgram/Soundness.lean)), where soundness theorems are typically
`propext`-clean rather than fully axiom-free.

## See also

- [../README.md](../README.md) — the Judgment layer overview.
- [../PPMProgram/README.md](../PPMProgram/README.md) — whole-program PPM sequencing and soundness built on this judgment.
