# PPM

> The QMeas measurement-based language (level `L_PPM`): adaptive Pauli-product measurement programs over **logical** qubits.

PPM is the surface language whose every primitive maps one-to-one onto a native lattice-surgery operation: Pauli-product measurement, Pauli-frame byproduct update, destructive readout, and classical control. It operates entirely on logical qubits (`LQubit = ⟨block, index⟩`); physical qubits appear only after lowering to QStab/QClifford. In the LogicQ stack, PPM programs are emitted by the higher levels (PPR / Compiler Mixed IR), checked for legality by `TypeChecker.Judgment.PPMProgram`, and carry a small-step operational semantics from which the measurement-gadget frame tables are derived.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Umbrella import (`Syntax` + `Semantics`). |
| [Syntax.lean](Syntax.lean) | Pure-data AST: `Sign`, `PLetter`, `MTarget`, `Stmt`, well-formedness predicates, and the Litinski gadget programs (`progHAt`, `progSAt`, `progCNOTAt`, `progCZAt`, `checkPlus`). |
| [Semantics.lean](Semantics.lean) | Small-step `Step`/`Steps` relation, the Pauli frame, the parametric `QInterp` state interface, derived head-of-sequence reductions, and the H-gadget frame-table theorem. |

## Key definitions

```lean
inductive Stmt
  | meas    (r : CVar) (P : MTarget)
  | frame   (q : LQubit) (p : PLetter)
  | discard (q : LQubit)
  | ite     (r : CVar) (s₁ s₂ : Stmt)
  | forLoop (n : Nat) (body : Stmt)
  | skip
  | seq     (s₁ s₂ : Stmt)
  | abort
```
(`PPM.Stmt`, [Syntax.lean](Syntax.lean))

```lean
/-- The QMeas measurement alphabet is restricted to single- and two-qubit
    logical Pauli observables (the natively lattice-surgery-realizable ones). -/
def MTarget.wf (P : MTarget) : Bool :=
  let qs := P.map Prod.fst
  (P.length = 1 || P.length = 2) && qs.Nodup
```
(`PPM.MTarget.wf`, [Syntax.lean](Syntax.lean))

```lean
/-- The measurement back-action interface: `proj P s ρ` is the normalized
    projection of `ρ` onto the `s`-eigenspace of the logical Pauli product `P`. -/
structure QInterp (Q : Type) where
  proj : MTarget → Sign → Q → Q

inductive Step (I : QInterp Q) : Config Q → Label → Config Q → Prop
```
(`PPM.QInterp`, `PPM.Step`, [Semantics.lean](Semantics.lean))

```lean
theorem progH_frame (I : QInterp Q) (ρ : Q) (s₁ s₂ : Sign) :
    ∃ ℓ ρ' σ' F',
      Steps I ⟨ρ, Store.empty, Frame.id0, progH⟩ ℓ ⟨ρ', σ', F', .skip⟩ ∧
      F' (ancQ 0) = hByp s₁ s₂
```
(`PPM.progH_frame`, [Semantics.lean](Semantics.lean))

## Example

The straight-line PPM fragment has a real text parser — it **parses today** by `decide` ([Parse.lean](Parse.lean)). Logical qubits are written `block[index]` with square brackets (`q[0]`, `a[0]`), classical outcomes are `c<n>`, and a measurement target is a comma-separated list of `LQubit ↦ PLetter` factors:

```text
c0 := M q[0]↦Z, a[0]↦X      -- M_{ZX}(q[0], a[0]) — a 2-body joint logical measurement
c1 := M q[0]↦X              -- M_X(q[0]) — a single-qubit logical measurement
frame Z(q[0])               -- record a Z byproduct on q[0]
discard q[0]                -- retire logical qubit q[0]
skip; abort                 -- newline/';'-separated statements
```

Block names (`q`, `a`, …) map to `Logical.BlockId`s in first-occurrence order, so `q` interns to block `0` and `a` to block `1`. The two-body line above parses to the `MTarget` value (machine form, [Syntax.lean](Syntax.lean)):

```lean
[.meas 0 [(⟨0, 0⟩, .Z), (⟨1, 0⟩, .X)]]   -- c0 := M q[0]↦Z, a[0]↦X
```

The native measurement alphabet requires one or two factors with no repeated logical qubit (`MTarget.wf`); a repeated qubit such as `c0 := M q[0]↦Z, q[0]↦X` parses but is structurally rejected by `MTarget.wf`. Source: [Parse.lean](Parse.lean) (lines 132-145), [Syntax.lean](Syntax.lean) (lines 183-185).

## Status & scope

- **Proved (P).** The small-step semantics is mechanized: `Steps.trans`, `Steps.single`, `abort_stuck` (no rule fires on `abort` — it is a genuine stuck terminal), the derived head-of-sequence combinators (`red_meas`, `red_ite_pos`, `red_ite_neg_frame`, `red_ite_pos_into`, `red_ite_neg_into`), the Hadamard-gadget frame table `progH_frame` (all four outcome branches `(+,+)→I, (+,-)→X, (-,+)→Z, (-,-)→Y`), and the post-selection `checkPlus_accepts` / `checkPlus_rejects`. The rewrite `MTarget.wf_eq` holds by `rfl`.
- **Tested (D).** The `MTarget.wf` alphabet restriction is exercised by `by decide` examples in [Syntax.lean](Syntax.lean).
- **Assumed / deferred (A).** The quantum state `Q` is **parametric** via `QInterp.proj`; the frame-correction results hold for **any** carrier `Q` and make no claim about a concrete projector's channel correctness. The gadget programs (`progHAt`, `progSAt`, `progCNOTAt`, `progCZAt`) are the Litinski lattice-surgery forms; their exact measurement pattern + channel correctness are the **ideal-gadget assumption** (deferred). `progCZAt` is explicitly flagged a DEMO placeholder (M16) that is shaped to type-check, not proved.
- **Out of scope here.** Program-level legality (legal measurements, bound classical outcomes for branches, no use-after-discard) is checked elsewhere, in `TypeChecker.Judgment.PPMProgram`, not in this folder. Distance, decoder, and fault-tolerance claims are not made at this level.

These are operational-semantics theorems over the AST; per the contract, soundness-style results are `propext`-clean rather than "axiom-free".

## See also

- [../README.md](../README.md) — LogicQ repository root and stack overview.
- [../PPR/README.md](../PPR/README.md) — the PPR level above PPM (Pauli-product rotations).
- [../TypeChecker/Judgment/PPMProgram/README.md](../TypeChecker/Judgment/PPMProgram/README.md) — the PPM-program legality judgment.
- [../TypeChecker/PPM/README.md](../TypeChecker/PPM/README.md) — PPM-related type-checker support.
