# TypeChecker/PPM

> Reserved namespace for PPM-specific checker adapters — currently a stub.

This directory is a placeholder in the LogicQ TypeChecker layer (the legality
stage that sits between front-end ChainQ code families and the Compiler Mixed IR).
It is intended for future PPM-specific checker adapters. As of now it contains
**no `.lean` modules and no subfolders** — the live PPM (Pauli-product measurement)
legality rules live one level over, under
[`TypeChecker/Judgment/PPM`](../Judgment/PPM/README.md) and
[`TypeChecker/Judgment/PPMProgram`](../Judgment/PPMProgram/README.md).

## What's here

| Module | Role |
| --- | --- |
| _(none yet)_ | Reserved namespace; the only file present is this `README.md`. |

The actual rules referenced below are **not** in this folder. They are quoted only
to point you at where the PPM checker really lives:

| Where the real code lives | Role |
| --- | --- |
| [`../Judgment/PPM/Check.lean`](../Judgment/PPM/Check.lean) | `checkPPM`, the proof-carrying capability matcher for a single logical PPM. |
| [`../Judgment/PPMProgram/Check.lean`](../Judgment/PPMProgram/Check.lean) | `checkPPMProgram`, SSA/dead-set well-formedness for whole PPM programs. |
| [`../Judgment/PPMProgram/Soundness.lean`](../Judgment/PPMProgram/Soundness.lean) | `∀` soundness theorems for the program checker. |

## Key definitions

These are the signatures this stub *defers to* (from the sibling folders above),
not definitions in this folder:

- The single-measurement matcher (`TypeChecker/Judgment/PPM/Check.lean`):

```lean
def checkPPM (Γ : TypedEnv) (caps : List Capability) (P : PPM.MTarget) :
    Except TypeError TypedPPM
```

- The program checker (`TypeChecker/Judgment/PPMProgram/Check.lean`):

```lean
def checkPPMProgram (Γ : TypedEnv) (caps : List Capability) (s : Stmt) :
    Except TypeError PPMState :=
  checkPPMStmt Γ caps PPMState.init s
```

## Example

This folder has only a stub header file. Quoted verbatim, its entire content is:

```text
# TypeChecker/PPM

Reserved for PPM-specific checker adapters.

Current PPM legality rules live under `TypeChecker/Judgment/PPM` and
`TypeChecker/Judgment/PPMProgram`.
```

(from the previous [README.md](README.md), preserved here as the honest state of
the directory.)

The PPM measurements these checkers vet are the ones produced by the PPM surface
language (parses today — `PPM/Parse.lean`, by `decide`). A single-body and a
two-body joint logical measurement, plus a frame and a discard, look like:

```text
c0 := M q[0]↦Z
c1 := M q[0]↦Z, a[0]↦X
frame Z(q[0])
discard q[0]
```

Each `c<n> := M …` parses to a `PPM.Stmt.meas r P` with target `P : PPM.MTarget`
(the `MTarget` value `checkPPM` is handed); e.g. the two-body line above is the
machine-form AST:

```lean
PPM.Stmt.meas 1 [(⟨0, 0⟩, .Z), (⟨1, 0⟩, .X)]
```

Block names map to `Logical.BlockId`s in first-occurrence order (`q ↦ 0`,
`a ↦ 1`).

For a real, load-bearing example, the program-checker soundness
theorem in the sibling folder states that every measurement a type-checked
statement emits passes `checkPPM`:

```lean
theorem checkPPMStmt_meas_sound (Γ : TypedEnv) (caps : List Capability) :
    ∀ (s : Stmt) (st st' : PPMState),
      checkPPMStmt Γ caps st s = .ok st' →
      (measTargets s).all (fun P => ok? (checkPPM Γ caps P)) = true
```

— cited from [`../Judgment/PPMProgram/Soundness.lean`](../Judgment/PPMProgram/Soundness.lean).

## Status & scope

- **This folder: M (missing/planned).** No modules yet; reserved namespace only.
  Nothing here is built, proved, or wired.
- The real PPM checker it points to is implemented elsewhere. In contract terms,
  `checkPPM`/`checkPPMProgram` are static legality judgments; the program-checker
  soundness results (e.g. `checkPPMStmt_meas_sound`) are **P (proved theorems)**,
  typically `propext`-clean rather than axiom-free.
- The capability matcher admits a cross-block PPM only against an installed
  merged-code certificate, and it explicitly **defers (A — documented assumption)**
  the per-construction physical obligations — merged-code distance, fault distance
  `R ≥ d`, relative expansion `β_d ≥ 1`, decoder existence, Cheeger bounds, etc.
  (see `ppmObligations` in [`../Judgment/PPM/Check.lean`](../Judgment/PPM/Check.lean)).
  Those channel-correctness, fault-tolerance, distance, and decoder claims are
  **not** discharged here.

## See also

- Parent layer: [`../README.md`](../README.md) (TypeChecker)
- Real rules: [`../Judgment/PPM/README.md`](../Judgment/PPM/README.md) and
  [`../Judgment/PPMProgram/README.md`](../Judgment/PPMProgram/README.md)
- Judgments overview: [`../Judgment/README.md`](../Judgment/README.md)
