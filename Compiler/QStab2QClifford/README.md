# Compiler/QStab2QClifford

> Lower physical stabilizer measurements (QStab) to concrete Clifford+measurement circuits (QClifford), choosing a per-`Prop` syndrome-extraction scheme.

This is the QStab -> QClifford pass at the bottom of the LogicQ stack: above it, ChainQ code families and the TypeChecker establish logical legality, the Compiler Mixed IR / PPM / LS layers schedule logical operations, and QStab expresses the resulting physical Pauli measurements + classical parities in SSA form. This pass picks an extraction **scheme** for each QStab `Prop` (standard X/Z, destructive X/Z, Shor cat+verifier, Knill transversal, single flag, double flag) and emits a `QClifford.Circuit`. The gadget plumbing is a **normalized port** of the sibling project **LeanQEC** (`QStab/QClifford/{Standard,Shor,Knill,FlagGeneral,Flag2General}.lean`): each gadget's quantum plumbing is kept faithful, but its `measZ`s are factored into one generic `measGroup` loop followed by one classical `parity`. Only the **X-type** flag schemes (`flagX`/`flag2X`) are implemented.

## What's here

| Module | Role |
|---|---|
| [Trace.lean](Trace.lean) | `traceHost`, `traceFold`, the linchpin `run_traceHost` (`run = traceFold`), the generic measurement loop, and `noMeasParity` no-op blocks |
| [Scheme.lean](Scheme.lean) | `ExtractionSpec` (scheme + qubits), `measuredList`/`measCount`/`syndromeOffsets`, schedule well-formedness `extractionSpecOk` |
| [Standard.lean](Standard.lean) | direct single-measurement gadgets (standard X/Z, destructive X/Z) |
| [Shor.lean](Shor.lean) | cat-state + verifier plumbing (`shorXPlumbing`/`shorZPlumbing`) |
| [Knill.lean](Knill.lean) | transversal-CNOT plumbing (`knillXPlumbing`/`knillZPlumbing`) |
| [Flag.lean](Flag.lean) | single-flag and two-flag plumbing |
| [Compile.lean](Compile.lean) | `compileProp` dispatch, `compile?`, and the trace-correctness / source-bridge theorems |
| [Basic.lean](Basic.lean) | aggregate, smart constructors, and all worked examples |

## Key definitions

The per-`Prop` extraction scheme — pure data, distinctness checked by a Boolean schedule check ([Scheme.lean](Scheme.lean)):

```lean
inductive ExtractionSpec
  | standardX (order : List PQubit) (anc : PQubit)
  | standardZ (order : List PQubit) (anc : PQubit)
  | destructiveX (q : PQubit)
  | destructiveZ (q : PQubit)
  | shorX (order : List PQubit) (cats : List PQubit) (ver : PQubit)
  | shorZ (order : List PQubit) (cats : List PQubit) (ver : PQubit)
  | knillX (order : List PQubit) (ancs : List PQubit)
  | knillZ (order : List PQubit) (ancs : List PQubit)
  | flagX (order : List PQubit) (anc : PQubit) (flag : PQubit)
  | flag2X (order : List PQubit) (anc : PQubit) (flag1 : PQubit) (flag2 : PQubit)
  deriving Repr, Inhabited
```

The checked compiler and its schedule checker ([Compile.lean](Compile.lean), [Scheme.lean](Scheme.lean)):

```lean
def compile? (cfg : CompileConfig) (p : QStab.Prog) : Except CompileError Circuit :=
  if p.wf then
    if specsOk cfg p then .ok (compile cfg p) else .error .badExtractionSchedule
  else .error .sourceMalformed

def extractionSpecOk (P : QStab.PauliString) (spec : ExtractionSpec) : Bool
```

The trace-host classical-dataflow contract and the source-semantics bridge ([Compile.lean](Compile.lean)):

```lean
theorem compile?_trace_correct {cfg : CompileConfig} {p : QStab.Prog} {c : Circuit}
    (h : compile? cfg p = .ok c) (outcome : Nat → Bool) :
    QClifford.run (traceHost outcome) c { next := 0 } QClifford.Store.empty
      = ({ next := totalMeas cfg p 0 },
          applyQStabClassicalGen cfg p 0 p.length 0 0 outcome QClifford.Store.empty)

theorem compile?_trace_evalVar {cfg : CompileConfig} {p : QStab.Prog} {c : Circuit}
    (h : compile? cfg p = .ok c) (outcome : Nat → Bool) (w : Nat) (hw : w < p.length) :
    (QClifford.run (traceHost outcome) c { next := 0 } QClifford.Store.empty).2 w
      = QStab.evalVar p (extractedOutcome cfg outcome) w
```

## Example

The **source** side of this bridge is a QStab `Prog` — physical Pauli measurements and classical parities in SSA form. QStab has a real text parser (parses today — [QStab/Parse.lean](../../QStab/Parse.lean), `by decide`), so the README readout program ([QStab/Syntax.lean:80](../../QStab/Syntax.lean#L80)) — a distance-3 repetition-style syndrome + logical readout — is written in QStab surface syntax:

```rust
// QStab source program (the input to this pass) — parses today (QStab/Parse.lean):
c0 = Prop[r=0,s=0] ZZI     // measure physical Pauli ZZI at round 0, slot 0
c1 = Prop[r=0,s=1] IZZ
c2 = Prop[r=1,s=0] ZZI
d0 = Parity c0 c2          // d0 = c0 ⊕ c2
c3 = Prop[r=1,s=1] IZZ
d1 = Parity c1 c3          // d1 = c1 ⊕ c3
c4 = Prop ZZZ              // scheduling coords optional
o0 = Parity c4             // o0 = c4
```

That text parses to exactly the `QStab.progReadout` AST value (the machine form actually passed to this pass) — `QStab.Parse.parsesTo readoutSrc QStab.progReadout = true` ([QStab/Parse.lean:104](../../QStab/Parse.lean#L104)):

```lean
-- QStab.progReadout : QStab.Prog  (the parsed AST — machine form):
[ .prop (some ⟨0, 0⟩) (ofString "ZZI"),   -- c0
  .prop (some ⟨0, 1⟩) (ofString "IZZ"),   -- c1
  .prop (some ⟨1, 0⟩) (ofString "ZZI"),   -- c2
  .parity [0, 2],                          -- d0 = c0 ⊕ c2
  .prop (some ⟨1, 1⟩) (ofString "IZZ"),   -- c3
  .parity [1, 4],                          -- d1 = c1 ⊕ c3
  .prop none (ofString "ZZZ"),             -- c4
  .parity [6] ]                            -- o0 = c4
```

The extraction schedule is itself pure data — one `ExtractionSpec` per prop. The standard-Z spec `stdZ 3 [1, 0]` (ancilla qubit 3, data qubits 1 then 0) lowers a single prop to the **target** QClifford circuit below — a fresh `|0⟩` ancilla (qubit 3), data qubits 1 and 0 control CNOTs into it, then one measurement into result bit 7. QClifford also has a real text parser (parses today — [QClifford/Parse.lean](../../QClifford/Parse.lean), `by decide`), so the emitted circuit for that prop is written in QClifford surface syntax:

```rust
// Spec for one prop (this pass's pure data): ExtractionSpec.standardZ [1, 0] 3
// Emitted QClifford circuit for that prop — parses today (QClifford/Parse.lean):
Prep0 q3        // fresh |0⟩ ancilla
CNOT q1 q3      // data qubit 1 → ancilla
CNOT q0 q3      // data qubit 0 → ancilla
Meas q3 -> c7   // measure ancilla into result bit 7
```

That text parses to exactly the emitted `QClifford.Circuit` AST value, byte-identical to the pre-M23 pass ([Basic.lean:61](Basic.lean#L61)) — `QClifford.Parse.parsesTo … [.prepZero 3, .CNOT 1 3, .CNOT 0 3, .meas 3 7] = true` ([QClifford/Parse.lean:115](../../QClifford/Parse.lean#L115)):

```lean
-- Emitted QClifford.Circuit (the gadget value — machine form):
[ .prepZero 3,    -- fresh |0⟩ ancilla
  .CNOT 1 3,      -- data qubit 1 → ancilla
  .CNOT 0 3,      -- data qubit 0 → ancilla
  .meas 3 7 ]     -- measure ancilla into result bit 7
```

The full program `progReadout` extracted under `repetitionReadoutCfg` (every prop a `stdZ 3 …`) gives a circuit with `measCount = 5` (one per prop) and `parityCount = 3` (`d0`, `d1`, `o0`) ([Basic.lean:57](Basic.lean#L57)). Source: [Basic.lean](Basic.lean) (§1).

The same file exercises the source-semantics bridge end to end. The bridge program is a Knill `ZZ` prop followed by a `Parity` ([Basic.lean:188](Basic.lean#L188)) — in QStab surface syntax (parses today — [QStab/Parse.lean](../../QStab/Parse.lean)):

```rust
// The source-bridge program (bridgeProg) — extracted with knillZ [0,1] [2,3]:
c0 = Prop ZZ        // the Knill ZZ prop (var 0)
d0 = Parity c0      // a parity of it (var 1)
```

```lean
-- bridgeProg : QStab.Prog  (the corresponding AST — machine form):
[ .prop none (ofString "ZZ"),   -- the Knill ZZ prop (var 0)
  .parity [0] ]                  -- a parity of it (var 1)
```

On every source variable, under the extraction-induced outcome stream (each prop's syndrome = the XOR of its physical measurements), the compiled store equals `QStab.evalVar bridgeProg …` — this is exactly the `compile?_trace_evalVar` bridge theorem instantiated at `bridgeProg` ([Basic.lean](Basic.lean) §6).

## Status & scope

This is a **classical-dataflow / compiler-correctness** contract ONLY.

- **Proved (`P`).** `compile?_trace_correct` proves the emitted circuit, run on the measurement-**trace** host, realises exactly the QStab SSA classical dataflow into the QClifford store; `compile?_trace_evalVar` bridges this to the QStab source semantics (`QStab.evalVar`) on every source variable; `propStoreUpdate_resultVar` makes each prop's result var equal to its extraction-local syndrome. These are `propext`-style soundness results (NOT advertised as "axiom-free"). Supporting lemmas (`run_traceHost`, `traceFold_compileProp`, the `evalStore` bridge chain) are likewise proved.
- **`by decide` tests (`D`).** All worked examples in [Basic.lean](Basic.lean): byte-identical standard gadgets, Shor/Knill/Flag/Flag2 measurement and parity counts, bad-schedule rejection (wrong support/basis, duplicate support, wrong ancilla count, flag2 out of scope, and the M23 helper-aliasing fix), and concrete trace-dataflow bit values.
- **Deferred / NOT proved (`A`/`M`).** This pass does **not** prove fault tolerance, code distance, hook-error detection, the Shor verifier / flag weight bounds, or the physical stabilizer-channel (Heisenberg) semantics. Those live in LeanQEC's `propagateGate`/`computeFaultEffect` layer — a different semantics from `QClifford.run` — and are not reproved here. Grouping each gadget's `measZ`s at the end is proved identical for the **trace** semantics; on disjoint qubits it is *expected* to be real-host-equivalent to the interleaved LeanQEC form, but **that real-host equivalence is NOT proved** here (only the plumbing's trace no-op is, and no real stabilizer host is defined in this folder).

## See also

- [../README.md](../README.md) — the Compiler layer overview
- [../../README.md](../../README.md) — LogicQ repository root
- This folder has no child directories with their own READMEs.
