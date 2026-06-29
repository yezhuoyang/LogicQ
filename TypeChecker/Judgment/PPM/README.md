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

The environment, the measurement targets, and the adapter capability are all DATA. A `PPM.MTarget` is the
machine form of a PPM measurement: the joint `Z̄ ⊗ Z̄` target below is what the PPM surface statement
`c0 := M q[0]↦Z, r[0]↦Z` parses to — the two distinct block names `q`, `r` intern to block ids 0, 1 in
first-occurrence order (PPM surface syntax parses today — [PPM/Parse.lean](../../../PPM/Parse.lean)).
This judgment checks the AST directly; it adds no surface keywords of its own. The bare qubit `q0`, the
`[[3,1,1]]` repetition code `rep`, and the joint `Z̄ ⊗ Z̄` target `zzTarget`
([Examples.lean:17-31](Examples.lean#L17-L31)):

```lean
-- the two data codes that populate the environment:
def q0 : Block := { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }
def rep : Block :=                                                 -- the [[3,1,1]] repetition code
  { n := 3,
    stab := [[false, false, false, true,  true,  false],
             [false, false, false, false, true,  true ]],
    lx := [[true,  true,  true,  false, false, false]],            -- X̄ = XXX
    lz := [[false, false, false, true,  false, false]] }           -- Z̄ = ZII

-- the joint Z̄(block 0) ⊗ Z̄(block 1) lattice-surgery target
-- (PPM surface form: `c0 := M q[0]↦Z, r[0]↦Z`, with q↦block 0, r↦block 1):
def zzTarget : PPM.MTarget := [(⟨0, 0⟩, PPM.PLetter.Z), (⟨1, 0⟩, PPM.PLetter.Z)]

-- the adapter capability whose connection stabilizer is the joint Z ⊗ Z₀ operator:
def zzCap : Capability :=
  { kind := .adapterPPM, blocks := [0, 1], ancN := 0,
    connStab := [[false, false, false, false, true, true, false, false]] }
```

Applying `checkPPM` to these values, over the environments `tenvQ = ⟨[q0]⟩` and `tenvQR = ⟨[q0, rep]⟩`:

```lean
-- targets shown as the PPM.MTarget AST; the PPM surface form (parses today,
-- PPM/Parse.lean) is given alongside each in `c<r> := M …↦…` syntax.

-- env tenvQ = ⟨[q0]⟩, no capabilities — PPM: `c0 := M q[0]↦Z`:
[(⟨0, 0⟩, PPM.PLetter.Z)]                                  -- OK: single-block Z̄ is native (weight-1)

-- env tenvR = ⟨[rep]⟩, no capabilities — PPM: `c0 := M q[0]↦X`:
[(⟨0, 0⟩, PPM.PLetter.X)]                                  -- OK: single-block X̄ = XXX is a logical op of rep

-- env tenvQR = ⟨[q0, rep]⟩, the DRIVING joint Z̄ ⊗ Z̄ target zzTarget
-- (PPM: `c0 := M q[0]↦Z, r[0]↦Z`):
[(⟨0, 0⟩, .Z), (⟨1, 0⟩, .Z)]   with caps []               -- rejected: cross-code joint PPM, no capability
[(⟨0, 0⟩, .Z), (⟨1, 0⟩, .Z)]   with caps [zzCap]          -- OK: a valid adapter capability supplies the merge
[(⟨0, 0⟩, .Z), (⟨1, 0⟩, .Z)]   with caps [{zzCap with connStab := []}]
                                                           -- rejected: degenerate cap (no connection) fails the
                                                           --           merged-code certificate
```

A joint `Z̄ ⊗ Z̄` measurement across a bare qubit and the `[[3,1,1]]` repetition code is rejected with no
capability, admitted only when an adapter capability supplies a valid merge, and rejected again when that
capability has no connection stabilizer. Source: [Examples.lean](Examples.lean).

The matcher also enforces target shape and row safety; the rejected targets carry a structured `TypeError`:

```lean
-- targets as PPM.MTarget AST; PPM surface form (PPM/Parse.lean) noted where one exists.

-- env tenvQ = ⟨[q0]⟩, no capabilities:
[]                                                         -- rejected: emptyMeasurement (no identity/no-op surface form)
[(⟨0, 0⟩, .X), (⟨0, 0⟩, .Z)]                              -- PPM `c0 := M q[0]↦X, q[0]↦Z`: rejected nonNativeMeasurement (repeats ⟨0,0⟩)
[(⟨0, 5⟩, .Z)]                                            -- PPM `c0 := M q[5]↦Z`: rejected badLogicalIndex 0 5 (out of range)

-- env tenvQR = ⟨[q0, rep]⟩, no capabilities:
[(⟨0, 0⟩, .Z), (⟨1, 0⟩, .Z), (⟨1, 0⟩, .X)]               -- PPM `c0 := M q[0]↦Z, r[0]↦Z, r[0]↦X`: rejected nonNativeMeasurement (>2 factors)
```

A malformed block — a zero-width logical, `badBlk = { n := 1, stab := [], lx := [[]], lz := [[]] }` — is
`Block.valid badBlk = false`, so it is UNREPRESENTABLE in a `TypedEnv`; the raw `checkPPMFromEnv` wrapper
rejects it at the boundary with `malformedBlock 0`, while a good raw env (`{ blocks := [q0] }`) is accepted.
Source: [Examples.lean](Examples.lean).

## Status & scope

The values above are confirmed by `by decide` executable tests (tier **D**) showing that `checkPPM` accepts /
rejects the right targets; the entire example set in [Examples.lean](Examples.lean) is `by decide`-closed. The certificate checks
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
