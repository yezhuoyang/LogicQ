# TypeChecker/Judgment/PPMProgram

> Whole-program well-formedness checking for PPM statements: SSA outcomes, frame/discard legality, and use-after-discard resource safety.

This folder implements the static legality checker for a PPM *program* (a tree of `Stmt`: measure, frame, discard, if-then-else, for-loop, seq). It threads an abstract `PPMState` (classical outcomes bound so far + the set of discarded logical qubits) through the statement and refuses anything that measures a discarded qubit, rebinds an outcome, branches on an unbound outcome, or targets an out-of-range / dead logical qubit. It sits in the TypeChecker legality layer above per-measurement `checkPPM` ([../PPM/](../PPM/README.md)) and below the Compiler Mixed IR lowering that lifts legal PPM steps into Mixed steps; operational stepping itself lives in `PPM.Semantics`, not here.

## What's here

| Module | Role |
| --- | --- |
| [DeadSet.lean](DeadSet.lean) | Mathlib-free normalized finite set of logical qubits (`insert`/`union`/`subset`) used to track discarded qubits, plus its membership lemmas |
| [State.lean](State.lean) | The abstract program state `PPMState` (`bound`, `dead`), `PPMState.init`, and `validLQubit` (block exists, live, index in range) |
| [Check.lean](Check.lean) | The checker `checkPPMStmt` / `checkPPMProgram`, plus the site collectors `measTargets` / `frameDiscardTargets` / `touches` used by soundness |
| [Soundness.lean](Soundness.lean) | The `∀` soundness theorems: every emitted measurement legal, every frame/discard target valid, dead-set monotone, no use-after-discard |
| [Examples.lean](Examples.lean) | `by decide` acceptance/rejection tests over the bare-qubit envs `tenvQ` / `tenvQR` |

The aggregator `TypeChecker.Judgment.PPMProgram` lives one level up as [`../PPMProgram.lean`](../PPMProgram.lean); it re-exports all of the above so `import TypeChecker.Judgment.PPMProgram` resolves `PPMState` / `validLQubit` / `checkPPMProgram` and the soundness theorems.

## Key definitions

```lean
structure PPMState where
  bound : List CVar
  dead  : DeadSet
  deriving Repr, Inhabited
```
(from [State.lean](State.lean) — classical outcomes bound so far, plus the normalized set of discarded logical qubits)

```lean
def validLQubit (Γ : TypedEnv) (q : LQubit) : Bool :=
  match Γ.block? q.blk with
  | some tb => tb.block.live && decide (q.idx < tb.block.lx.length)
  | none    => false
```
(from [State.lean](State.lean) — a logical qubit's block must exist, be live, and have an in-range index)

```lean
def checkPPMStmt (Γ : TypedEnv) (caps : List Capability) :
    PPMState → Stmt → Except TypeError PPMState
```
```lean
def checkPPMProgram (Γ : TypedEnv) (caps : List Capability) (s : Stmt) :
    Except TypeError PPMState :=
  checkPPMStmt Γ caps PPMState.init s
```
(from [Check.lean](Check.lean) — the statement-level checker threading `PPMState`, and the program entry point starting from `PPMState.init`)

```lean
theorem checkPPMStmt_no_use_after_discard (Γ : TypedEnv) (caps : List Capability) (q : LQubit) :
    ∀ (s : Stmt) (st st' : PPMState),
      checkPPMStmt Γ caps st s = .ok st' →
      st.dead.contains q = true → touches s q = false
```
(from [Soundness.lean](Soundness.lean) — a type-checked statement never references a qubit already discarded)

## Example

This checker runs over the PPM `Stmt` AST defined in [`PPM/Syntax.lean`](../../../PPM/Syntax.lean). The straight-line fragment of that AST has a real text parser ([`PPM/Parse.lean`](../../../PPM/Parse.lean) — parses today by `decide`), whose surface forms are:

```text
c0 := M q[0]↦Z              -- one-body measurement, outcome bound to c0
c0 := M q[0]↦Z, a[0]↦X      -- two-body joint measurement (q interns to block 0, a to block 1)
frame Z(q[0])               -- record a Z byproduct frame on q[0]
discard q[0]                -- retire logical qubit q[0]
skip                        -- do-nothing
abort                       -- post-selection terminal
```

Statements are `;`- or newline-separated; block names (`q`, `a`, …) map to block ids in first-occurrence order. The adaptive conditional (`if r = +1 then … else …`) and bounded `for` loops are in the BNF but are NOT yet in the text parser — they remain first-class in the `Stmt` AST only (`.ite` / `.forLoop`), so examples that exercise them are shown in **machine form** (the real Lean `Stmt` AST, where `;;` is `Stmt.seq`).

The checker is exercised over the bare-qubit env `tenvQ` (block `0`, one logical qubit `q[0]` = `⟨0,0⟩`). The following machine-form value pins the dead-set *union* join across an `.ite`:

```lean
-- ite branch UNION: discarding q[0] in ONE branch marks it dead afterward, so a
-- following frame is rejected (would be ACCEPTED under intersection/empty-join).
-- The .meas/.frame parts correspond to the PPM surface `c0 := M q[0]↦Z` and
-- `frame X(q[0])`; the `.ite` has no surface form yet (machine form only):
.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)] ;; .ite 0 (.discard ⟨0, 0⟩) .skip ;; .frame ⟨0, 0⟩ .X
-- rejected: useAfterDiscard 0 0 — discarded in one ite branch, then framed
```

Discarding `q[0]` (`⟨0,0⟩`) in only one branch of an `.ite` still marks it dead afterward (branch joins take the set *union* of the two branches' dead sets), so the subsequent frame on that qubit is rejected as a use-after-discard. This value discriminates the union join from an intersection/empty join. Source: [Examples.lean](Examples.lean).

## Status & scope

- **P (proved theorems, `propext`-clean soundness):** [Soundness.lean](Soundness.lean) proves, by induction over `Stmt`, that any statement accepted by `checkPPMStmt` satisfies: every measurement target passes `checkPPM` (`checkPPMStmt_meas_sound`), every frame/discard target satisfies `validLQubit` (`checkPPMStmt_targets_valid`), the dead set only grows (`checkPPMStmt_dead_mono`), and no qubit is referenced after being discarded (`checkPPMStmt_no_use_after_discard`). The supporting `DeadSet` membership lemmas in [DeadSet.lean](DeadSet.lean) are likewise proved.
- **D (`by decide` tests):** [Examples.lean](Examples.lean) pins acceptance and rejection cases (SSA outcome reuse, unbound branch outcome, bad logical index, dead block, empty measurement, double-discard, measure-after-discard, branch-union dead set, loop "discards nothing" via subset).
- **A / scope boundary:** this is *static* resource/legality checking only. Operational stepping for PPM lives in `PPM.Semantics` (out of this folder); the loop rule is conservative — a body that discards any logical qubit is rejected outright via `DeadSet.subset`, and branch-local outcome bindings do not escape an `ite`. No claim here about channel correctness, fault tolerance, distance, or operational equivalence — those remain deferred per the repo contract.

See the contract tiers in [Compiler/CONTRACT.md](../../../Compiler/CONTRACT.md) for the P / D / A / M conventions.

## See also

- Parent: [TypeChecker/Judgment/README.md](../README.md) · [TypeChecker/README.md](../../README.md) · repo root [README.md](../../../README.md)
- Per-measurement legality this checker calls into: [TypeChecker/Judgment/PPM/README.md](../PPM/README.md)
