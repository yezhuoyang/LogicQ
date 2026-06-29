# Compiler/Mixed

> The Mixed IR — the implemented compiler target: a single logical-execution IR that interleaves native PPM fragments, direct transversal Cliffords, logical CNOTs, code switches, deferred magic obligations, and logical Paulis.

This is **Stage 4** of the LogicQ stack and the IR the front-end actually lowers into. Source `LogicalOp` programs (the small Lean DSL) are compiled here by the resource-aware `compile?` (see [Lower/](Lower/README.md)); each `MixedInstr` is type-checked against a `TypedEnv` (from the TypeChecker / ChainQ code families) and a threaded PPM resource state, and given an evidence-carrying small-step `Step` semantics. From here the wired edges go on to the simulator (`Compiler.Simulator`) and the `PPM → QStab → QClifford` extraction path toward the physical stabilizer target.

## What's here

| Module | Role |
|---|---|
| [Syntax.lean](Syntax.lean) | Pure data layer: `MagicObligation`, the `MixedInstr` instruction set, source `LogicalOp`, the `2×2` symplectic gate matrices, `MixedInstr.action`, `singleLogicalBlock` |
| [Source.lean](Source.lean) | Source-level typing of `LogicalOp`: `srcAction`, `srcOpOk`, `progOpNext`, `sourceOpOk`, `sourceWellFormed` |
| [Check.lean](Check.lean) | The mixed-IR checker `checkInstr` / `checkLogicalExec` (threads `TypedEnv` + `PPMState`), plus the `private` legacy M9 cost-driven selector |
| [Semantics.lean](Semantics.lean) | The one shared evidence-carrying operational semantics: `MixedInterp`, `ExecState`, `Step` / `Steps`, per-instruction realization + progress lemmas, the `GadgetBoundary` tagging |
| [Lower.lean](Lower.lean) | Aggregator that imports the `Mixed/Lower/` resource-aware compilation relation + public `compile?` (see [Lower/](Lower/README.md)) |
| [Parse.lean](Parse.lean) | Keyword-led text parsers: `parseLogical` (the `Logical`-prefixed source language) and `parseMixed` (the kind-keyword Mixed IR), reusing the shared lexers + the PPM target parser; `by decide` round-trip tests |

## Key definitions

```lean
inductive MixedInstr
  | ppm          (s : PPM.Stmt)                          -- a native PPM/PPU fragment
  | transversal  (b : Nat) (g : BoolMat)                 -- a local single-qubit transversal gate
  | transversalCNOT (spec : TransversalCNOTSpec)          -- an inter-block incidence-checked logical CNOT
  | transversalCNOTBatch (spec : TransversalCNOTBatchSpec) -- a batched high-rate logical CNOT incidence
  | automorphism (b : Nat) (M : BoolMat)                 -- an arbitrary symplectic logical automorphism
  | switch       (b : Nat) (D : Block) (cert : SwitchCert)      -- a code switch (consumes/transforms b)
  | magic        (ob : MagicObligation)                  -- a deferred, TYPED magic-state obligation (e.g. T)
  | pauli        (q : LQubit) (p : PPM.PLetter)          -- a logical Pauli APPLIED to the carrier (M18: real op, not a frame record)
  deriving Repr
```

`checkInstr` threads both the typed environment `Γ` and the PPM resource state `st`; `magic` type-checks as a deferred obligation but has no operational semantics:

```lean
def checkInstr (caps : List Capability) :
    TypedEnv → PPMState → MixedInstr → Except TypeError (TypedEnv × PPMState)
```

`Step` is evidence-carrying — every rule has a `checkInstr … = .ok (Γ', R')` premise and steps to that checked `(Γ', R')`; there is no `magic` rule:

```lean
inductive Step (I : MixedInterp Q) (caps : List Capability) :
    MixedInstr → ExecState Q → ExecState Q → Prop
```

```lean
theorem Step_implies_checkInstr (I : MixedInterp Q) (caps : List Capability)
    (instr : MixedInstr) (s s' : ExecState Q) (h : Step I caps instr s s') :
    ∃ Γ' R', checkInstr caps s.env s.resource instr = .ok (Γ', R')
```

```lean
theorem no_step_magic (I : MixedInterp Q) (caps : List Capability) (ob : MagicObligation)
    (s : ExecState Q) : ¬ ∃ s', Step I caps (.magic ob) s s'
```

## Surface syntax — keyword-led, parses today

The two languages of this stage each have a real text parser ([Parse.lean](Parse.lean), tests by
`decide`). **The keywords ARE the constructors:** every **logical** instruction carries the
**`Logical`** keyword, and every **Mixed IR** instruction **leads with its kind keyword** (the
`MixedInstr` discriminator above).

![ppm](https://img.shields.io/badge/ppm-1f6feb) ![transversal](https://img.shields.io/badge/transversal-2ea44f) ![transversalCNOT](https://img.shields.io/badge/transversalCNOT-3fb950) ![transversalCNOTBatch](https://img.shields.io/badge/transversalCNOTBatch-238636) ![automorphism](https://img.shields.io/badge/automorphism-8957e5) ![switch](https://img.shields.io/badge/switch-d29922) ![magic](https://img.shields.io/badge/magic-da3633) ![pauli](https://img.shields.io/badge/pauli-009688)

```rust
// LogicalOp source — the `Logical` keyword is REQUIRED (parseLogical; a bare gate is rejected):
Logical H q[0]
Logical CNOT q[0] q[1]
Logical T q[0]
Logical measure q[0]↦Z -> c0

// MixedInstr — the KIND keyword leads (parseMixed):
transversal 0 H                  // MixedInstr.transversal 0 hGate2x2
transversalCNOT q[0] q[1] [[1]]  // MixedInstr.transversalCNOT {control, target, incidence}
pauli X q[0]                     // MixedInstr.pauli ⟨0,0⟩ .X
magic T q[0]                     // MixedInstr.magic {kind := .tGate, target := ⟨0,0⟩}
ppm c0 := M q[0]↦Z               // MixedInstr.ppm (.meas 0 [(⟨0,0⟩, .Z)])
// the remaining three are keyword-led; their matrix / Block / cert payload stays machine-form:
automorphism 0 [[ ..2n×2n.. ]]                          // MixedInstr.automorphism 0 M
switch 0 repCode3 { kind := .gaugeFix, f := encF }      // MixedInstr.switch 0 D cert
transversalCNOTBatch 0 1 [[1]] [[1]]                    // MixedInstr.transversalCNOTBatch {controlBlock,…}
```

All eight `MixedInstr` keywords appear above; `automorphism` / `switch` / `transversalCNOTBatch` carry
a full `BoolMat` / `Block` / `SwitchCert` payload, so text parsing for them is the next increment (the
other five round-trip by `decide` today).

## Example

The fixtures the program runs against — a one-block environment holding a single bare
qubit, and the `[[3,1,1]]` code it gets switched into (verbatim from
[TypeChecker/Judgment/Switch/Examples.lean:17](../../TypeChecker/Judgment/Switch/Examples.lean#L17)):

```lean
-- tsrc : TypedEnv — one bare logical qubit, n=1
unenc1 = { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }

-- repCode3 : Block — the [[3,1,1]] bit-flip repetition code (symplectic form, width 6)
{ n := 3,
  stab := [[false, false, false, true,  true,  false],    -- Z₀Z₁
           [false, false, false, false, true,  true ]],    -- Z₁Z₂
  lx := [[true,  true,  true,  false, false, false]],       -- X̄ = XXX
  lz := [[false, false, false, true,  false, false]] }      -- Z̄ = Z₀

-- encF : BoolMat — the encoding map X̄ ↦ XXX, Z̄ ↦ Z₀ (2 rows × 6)
[[true, true, true, false, false, false],
 [false, false, false, true, false, false]]

-- idMat 6 : BoolMat — the 6×6 identity over GF(2) (the 2·3×2·3 IDENTITY automorphism)
[[true,  false, false, false, false, false],
 [false, true,  false, false, false, false],
 [false, false, true,  false, false, false],
 [false, false, false, true,  false, false],
 [false, false, false, false, true,  false],
 [false, false, false, false, false, true ]]
```

These two programs — both `LogicalExec = List MixedInstr` values over `tsrc` — are the
checker's switch-env-threading discriminator. The IDENTITY automorphism `idMat 6` is a
2·3×2·3 map that is well-shaped ONLY for the n=3 post-switch block:

```lean
-- OK: encode the bare qubit (n=1) into the [[3,1,1]] code (n=3), THEN the identity
-- automorphism `idMat 6` — legal because block 0 is now n=3 after the switch.
[ .switch 0 repCode3 { kind := .gaugeFix, f := encF }
, .automorphism 0 (idMat 6) ]

-- rejected: the SAME automorphism WITHOUT the switch — block 0 is still n=1, so
-- `idMat 6` is not 2n×2n. (The checker threads the post-switch env through.)
[ .automorphism 0 (idMat 6) ]
```

These values show the checker threading the post-switch environment instruction-to-instruction: an automorphism legal only against the code produced by an earlier `switch`. Source: [Check.lean](Check.lean) (§5 executable tests).

## Status & scope

Honest scope, mirroring [`Compiler/CONTRACT.md`](../CONTRACT.md) tiers (**P** proved theorem, **D** `by decide` test, **A** documented assumption, **M** missing/planned):

- **Proved (P).** The `MixedInstr` / `LogicalOp` data and the `checkInstr` / `checkLogicalExec` checker are total functions. The `Step` / `Steps` semantics is *evidence-carrying*: `Step_implies_checkInstr`, `no_step_of_checkInstr_error`, and `no_step_magic` make the checked interface gap-free, and the per-instruction realization + progress lemmas (`Step_transversal_realizes`, `Step_pauli_realizes`, `transversal_step_matches_action`, `Steps_append`, the `progress_*` family) hold over an arbitrary carrier `Q`. The soundness theorems are typically `propext`-clean, **not** "axiom-free."
- **`by decide` instances (D).** The §5 tests in [Check.lean](Check.lean) exercise cost-driven selection, resource threading, use-after-discard across PPM fragments, and switch env-threading on concrete fixtures.
- **Deferred / assumed (A).** `magic` (e.g. `T`) **only type-checks** — it has no `Step` rule (`compile? .executable` excludes it via `progNoMagic`); MagicQ is unwired. The direct fragment is given a *symplectic* (Heisenberg-picture) semantics, the right notion for the symplectic checker; full unitary-with-phase equivalence is deferred. The PPM gadget steps prove **frame-level** progress (control flow + classical store + Pauli frame) only — the carrier *channel* correctness (`QInterp.proj`) is **assumed ideal** (`GadgetBoundary.idealChannel`). `progCZAt` is an experimental placeholder gadget (CZ stays out of the exact-operational fragment).
- **Not claimed here.** Fault tolerance, code distance, decoders, and the physical stabilizer channel are out of scope for this layer (see the contract matrix). `switch` preserves the logical state at the *ideal* level (a transparent coercion); the `SwitchCert` certificates are external/assumed.

## See also

- [Compiler/README.md](../README.md) — the compiler stack overview
- [Compiler/CONTRACT.md](../CONTRACT.md) — the per-stage proved/deferred contract matrix
- [Lower/README.md](Lower/README.md) — the resource-aware compilation relation + the public `compile?` (Source `LogicalOp` → Mixed IR)
