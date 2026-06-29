# Compiler.LS — the lattice-surgery IR (LSIR)

> The surgery-schedule / certificate IR shared by both lowering paths, sitting between the logical IRs (PPM, MagicQ) and the physical stabilizer-measurement IR (QStab).

LSIR is the missing surgery-schedule / certificate layer in the LogicQ stack. It sits
**after** the logical IRs (MagicQ cultivation, PPM) and **before** `QStab.StabilizerProg`
(which `QStab2QClifford` then lowers to the physical target):

```text
MagicQ cultivation ─┐
                    ├─► LS ─► QStab.StabilizerProg + detector/observable/postselect
PPM ────────────────┘                              sidecar ─► QStab2QClifford ─► physical
```

LSIR is **not** another QStab. QStab owns the physical Pauli measurements, the
Clifford/prep/feed-forward stabilizer instructions, and the SSA classical parity
dataflow. LSIR owns the surgical/control structure QStab intentionally does not:
patches/carriers, surgery rounds/slots, logical→physical measurement certificates,
stabilizer-flow contracts, detector/observable annotations (parity expressions over
measurement vars), postselection policy, and deferred fault/decoder/quality
obligations. Explicit AST (no parser/notation), Mathlib-free. Build:
`lake build Compiler.LS.Basic`.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Public aggregate (umbrella) importing every LS module. |
| [Syntax.lean](Syntax.lean) | The LS AST: `SPauli` (sparse Pauli + `wf`/`wfMeas`/`toDense`), `Frac`, `PostPred`/`PostPolicy`, `DeferredContract`, `Flow`, `DetectorAnn`, `LSOp`, `Program`, and `Program.dataflow`. |
| [Cert.lean](Cert.lean) | `SurgeryCert` + `FaultObligations`/`FaultStatus` (migrated here from `LS2QStab/Basic.lean`, now a shim). |
| [Check.lean](Check.lean) | `check` (SSA, scope, sparse-Pauli, flow structure, detector determinism) → `Checked` summary; `LSError`, `Obligation`, `LogicalMeasCertData`. |
| [LowerQStab.lean](LowerQStab.lean) | `lower`/`lowerChecked`/`lowerCheckedWithExtract` into `QStab.StabilizerProg` + sidecar; the `lower_dataflow` preservation theorem. |
| [Extract.lean](Extract.lean) | The QStab2QClifford extractability classifier (`uniformX`/`uniformZ`/`mixedOrY`) + `notExtractable` obligation for mixed/Y measurements. |
| [Geometry.lean](Geometry.lean) | Patch geometry metadata (`QubitCoord`/`Polygon`) over `Frac` (rational-capable) coordinates. |
| [Chunk.lean](Chunk.lean) | The generic `LSChunk`/`LoweredChunk` abstraction + chunk-aware lowering (code/layout/protocol agnostic). |
| [ChunkCompose.lean](ChunkCompose.lean) | Generic sequential composition of `List LSChunk` (QVar-offsetting + merge) + structural flow-interface matching. |
| [SyndromeRounds.lean](SyndromeRounds.lean) | Generic repeated syndrome-extraction chunk (real `prop` rounds + adjacent-round repeat detectors). |
| [PPM.lean](PPM.lean) | The PPM → LS adapter (requires a physical witness CONNECTED to the surgery certificate). |
| [MagicQ.lean](MagicQ.lean) | MagicQ cultivation → LS stage scaffold + the executable d3 H_XY-check subset lowering. |
| [Gidney/Basic.lean](Gidney/Basic.lean) | Compatibility shim re-exporting `Compiler.LS.Chunk` (the chunk infra is no longer Gidney-owned). |
| [Gidney/Cultivation.lean](Gidney/Cultivation.lean) | The real d=3 double-cat / H_XY check `gen.Chunk` (7-MX body + 6 detectors + 8 flows). |

## Key definitions

```lean
abbrev SPauli := List (PQubit × Pauli)

def SPauli.toDense (n : Nat) (P : SPauli) : PauliString

inductive LSOp
  | prepZero (q : PQubit) | prepPlus (q : PQubit) | h (q : PQubit) | s (q : PQubit)
  | sDag (q : PQubit) | x (q : PQubit) | z (q : PQubit)
  | cnot (control target : PQubit) | cz (a b : PQubit)
  | meas (sched : Option Sched) (P : SPauli) (kind : MeasKind := .mpp)
  | parity (srcs : List QVar) | detector (ann : DetectorAnn)
  | observable (name : String) (srcs : List QVar) | postselect (policy : PostPolicy)
  | stage (tag note : String) | tick | deferred (contract : DeferredContract)

structure Program where
  numQubits : Nat
  ops       : List LSOp
  flows     : List Flow := []

def Program.dataflow (p : Program) : QStab.Prog := p.ops.filterMap (LSOp.toStmt? p.numQubits)
```

The dataflow-preservation theorem (in [LowerQStab.lean](LowerQStab.lean)) is the
load-bearing result:

```lean
theorem lower_dataflow (p : Program) : (lower p).dataflow = p.dataflow
```

## Worked example — one program at every level of the stack

To see where LS sits, follow a real **QASMBench** program — `deutsch_n2` (2 qubits) —
from OpenQASM text down to physical `QStab`, running on a real quantum-LDPC code. Every
box below is an actual type / value in the tree (file:line cited). Levels 0–3 are a single
front-end pipeline (`Compiler.QASM.compileQASMToMixIR?`); levels 4–6 are the LS → QStab →
physical path that consumes the PPM / MagicQ fragments produced at level 3.

```text
QASM text ─►(parse)─► QASMProgram ─►(allocate onto a ChainQ code)─► ChainQPrimProgram
   level 0              level 1                                        level 2
        ─►(lower)─► MixedIR (List MixedInstr) ─►(PPM/MagicQ fragments)─► LS Program
                    level 3                                              level 4  ◄── THIS module
        ─►(lower)─► QStab.StabilizerProg + sidecar ─►(QStab2QClifford)─► QClifford / physical
                    level 5                                              level 6
```

### Level 0 — OpenQASM text (the input)

The `deutsch_n2` benchmark, embedded verbatim from pnnl/QASMBench
([Compiler/QASM/Benchmarks.lean:177](../QASM/Benchmarks.lean#L177)):

```qasm
OPENQASM 2.0;
qreg q[2];  creg c[2];
x q[1];  h q[0];  h q[1];  cx q[0],q[1];  h q[0];
measure q[0] -> c[0];  measure q[1] -> c[1];
```

### Level 1 — `QASMProgram` (parsed)

`parseOpenQASM2? : String → Except ParseError QASMProgram`
([Compiler/QASM/Parse.lean:266](../QASM/Parse.lean#L266)) produces:

```lean
{ qregs := [⟨"q", 2⟩], cregs := [⟨"c", 2⟩]
  instrs := [.x ⟨"q",1⟩, .h ⟨"q",0⟩, .h ⟨"q",1⟩, .cx ⟨"q",0⟩ ⟨"q",1⟩, .h ⟨"q",0⟩,
             .measure ⟨"q",0⟩ ⟨"c",0⟩, .measure ⟨"q",1⟩ ⟨"c",1⟩] }
```

### Level 2 — allocation onto a QEC code → `ChainQPrimProgram`

`allocate? : QASMProgram → AllocationRequest → Except QASMError Allocation`
([Compiler/QASM/Allocate.lean:193](../QASM/Allocate.lean#L193)) maps each virtual qubit
`q[i]` first-fit to a named logical qubit of a **ChainQ code block** supplied in
`AllocationRequest.decls`. The code can be any ChainQ code — including a real **lifted-product
qLDPC code** (Panteleev–Kalachev, [ChainQ/LiftedProduct/Basic.lean:19](../../ChainQ/LiftedProduct/Basic.lean#L19)):

```lean
ChainQ.Internal.liftedProduct 3 [[[0], [1]]] 1 2   -- ℓ=3, A = [1, x] ⇒ n = (1²+2²)·3 = 15, CSS ✓
```

(The *curated benchmark* suite allocates each virtual qubit to a **bare** block to isolate
the front-end; the code-family path [Compiler/Demo/Families.lean](../Demo/Families.lean) runs
surface / toric / HGP / lifted-product codes end-to-end.) Allocation emits a
`ChainQPrimProgram` of *named* ChainQ ops (`.xGate`, `.hGate`, `.cnotGate`, `.measure`, …,
[Compiler/ChainQ2Mixed/Compile.lean](../ChainQ2Mixed/Compile.lean)).

### Level 3 — MixedIR (`List MixedInstr`) — covering all the mixed-IR variants

`compileChainQToMixIR?` lowers to `LogicalExec = List MixedInstr`
([Compiler/Mixed/Syntax.lean:36](../Mixed/Syntax.lean#L36)) — the proof-carrying mixed
gate/measurement/surgery IR. **All eight** variants:

```lean
inductive MixedInstr
  | ppm                  (s : PPM.Stmt)                 -- native PPM/PPU fragment (measurements, gadgets)  ── feeds LS
  | transversal          (b : Nat) (g : BoolMat)        -- local single-qubit transversal (H, S)
  | transversalCNOT      (spec) | transversalCNOTBatch (spec)  -- inter-block (high-rate) logical CNOT
  | automorphism         (b : Nat) (M : BoolMat)        -- a symplectic logical automorphism
  | switch               (b : Nat) (D : Block) (cert : SwitchCert)  -- a code switch (reuses TypeChecker.checkSwitch)
  | magic                (ob : MagicObligation)         -- a deferred typed T-gate obligation  ── feeds MagicQ → LS
  | pauli                (q : LQubit) (p : PPM.PLetter) -- a logical Pauli applied to the carrier
```

`deutsch_n2` exercises three of them: `x`/`h` → `.pauli` / `.transversal`, `cx` →
`.transversalCNOT` (or a PPM CNOT gadget `.ppm`), and the two `measure`s → `.ppm (.meas …)`
(its real resource counts: 2 qubits, 7 mixed instructions, 2 measurements, 1 two-qubit gate —
[Benchmarks.lean:1384](../QASM/Benchmarks.lean#L1384)). A concrete compiled snippet — the
program `measure Z on q0 ; H q0` ([Compiler/Mixed/Lower/Examples.lean:26](../Mixed/Lower/Examples.lean#L26)):

```lean
[ .ppm (.meas 0 [(⟨0,0⟩, PPM.PLetter.Z)]), .transversal 0 hGate2x2 ]   -- hGate2x2 = [[F,T],[T,F]]
```

### Level 4 — LS (the surgery IR — **this module**)

The `.ppm` fragments (and, for `magic`, the MagicQ cultivation chunks) are exactly what LS
owns. The PPM → LS adapter `ppmMeasToLS?`
([PPM.lean:27](PPM.lean#L27)) turns a PPM measurement + physical witness into an LS `meas`
op (it *refuses* without a witness):

```lean
def ppmZZ     : PPM.MTarget := [(⟨0,0⟩, .Z), (⟨1,0⟩, .Z)]   -- a 2-body ZZ lattice-surgery readout
def witnessZZ : SPauli      := [(0, .Z), (1, .Z)]
-- ppmMeasToLS? (some ⟨0,0⟩) ppmZZ (some witnessZZ)  ⇒  .ok (.meas (some ⟨0,0⟩) [(0,.Z),(1,.Z)])
```

An LS `Program` carries those `meas` ops plus the surgery sidecar (detectors / observables /
postselection / flows). The canonical LS example ([Check.lean:272](Check.lean#L272)):

```lean
def goodProg : Program :=
  { numQubits := 2
    ops := [ .meas (some ⟨0,0⟩) [(0,.Z),(1,.Z)]                        -- c0 (binds QVar 0)
           , .meas (some ⟨1,0⟩) [(0,.Z),(1,.Z)]                        -- c1 (binds QVar 1)
           , .detector { name := "d0", srcs := [0,1], tags := ["color"] }  -- d0 = c0 ⊕ c1
           , .observable "o0" [0]
           , .postselect (.byDetector "d0")
           , .postselect (.byTag "color") ] }
```

### Level 5 — QStab (the physical stabilizer-measurement IR)

`lower : Program → QStab.StabilizerProg` ([LowerQStab.lean:46](LowerQStab.lean#L46)) maps each
executable LS op 1:1. `goodProg` becomes (densifying each sparse Pauli):

```lean
[ .bind (.prop (some ⟨0,0⟩) (ofString "ZZ")), .bind (.prop (some ⟨1,0⟩) (ofString "ZZ")) ]
```

The theorem `lower_dataflow` proves the classical dataflow `[.prop "ZZ", .prop "ZZ"]` is
**preserved**; the detector / observable / postselect ride in the sidecar (`Checked`), never
silently dropped.

### Level 6 — physical

`QStab2QClifford` ([Compiler/QStab2QClifford/Compile.lean](../QStab2QClifford/Compile.lean))
lowers each `.prop` to a concrete syndrome-extraction gadget (direct / Shor / Knill / flag) →
a QClifford circuit; `compile?_trace_correct` proves the circuit realizes the QStab classical
dataflow (the compiler dataflow contract — **not** fault tolerance).

### The LS well-formedness discipline (level 4, in detail)

A sparse Pauli used as an LS `meas` must be **non-empty**, **identity-free**,
**duplicate-qubit-free**, and **in range** for the patch, and it densifies to a
`QStab.PauliString` ([Syntax.lean](Syntax.lean)):

```lean
[(0, .Z), (1, .Z)]      -- OK: a 2-body ZZ readout (densifies on 3 qubits to "ZZI")
[(0, .Z), (2, .Z)]      -- OK: densifies on 3 qubits to "ZIZ"
[(0, .I)]               -- rejected: an identity factor
[(0, .Z), (0, .X)]      -- rejected: a duplicate qubit
[]                      -- rejected: an empty measurement
[(0, .Z), (5, .Z)]      -- rejected on a 2-qubit patch: out of range
```

## Status & scope

Honest tiering per [Compiler/CONTRACT.md](../CONTRACT.md) (P proved theorem, D `by decide`
test, A documented assumption, M missing/planned):

- **CHECKED (D / structural)** — sparse-Pauli validity (no identity/duplicate, non-empty
  for a measurement, in range, densification); SSA / scope (`parity`/`detector`/
  `observable`/`postselect` reference only already-bound vars; postselect references a
  known detector name / **detector tag** — stage tags do not satisfy detector-tag
  postselection); flow contracts *structurally* well-formed; detector determinism is
  **non-vacuous** (an out-of-range readout or malformed program returns `false`, not
  "deterministic"). The PPM adapter keeps the 1-or-2-body discipline and, with a cert,
  requires the witness to densify to the cert's measured parity.
- **LOWERED to QStab (P)** — executable LS ops (`prepZero`/`prepPlus`/`h`/`s`/`sDag`/`x`/
  `z`/`cnot`/`cz`/`meas`/`parity`) map 1:1 to `QStab.StabilizerInstr` (`meas` densifies to
  a physical `prop`). The theorem `lower_dataflow` (`propext`-only, **not** "axiom-free")
  proves the lowered `StabilizerProg`'s classical dataflow **equals** the LS program's
  dataflow — the measurement structure is preserved, not silently erased. Annotations are
  kept in the sidecar (`Checked`), never dropped.
- **DEFERRED (M / explicit `Obligation`s, never proven)** — full stabilizer-flow
  **semantic** soundness (`flowSemantics`, emitted for *every* flow regardless of
  `FlowStatus.structural`, which is never a soundness claim); code/fault distance and
  decoder threshold (`fault`, all `deferred`); the non-Pauli `H_XY` double-check, escape
  graft/transition, and stage chunks (`DeferredContract` — H_XY is **never** lowered to a
  fake Pauli measurement); downstream extractability (`Y`/mixed-X/Z measurements are
  `notExtractable` and recorded, never silently claimed executable); chunk composition
  matches flow interfaces **structurally** only (`flowCompositionDeferred`).
- **Closure** — invalid / wrong-code / multi-stage / unwitnessed protocols **refuse** with
  structured errors. Only two narrow subsets lower (the d3 double-cat **H_XY-check** subset
  and a generic **stabilize** subset); **full default cultivation** (injection / growth /
  escape graft+transition / output) and **15-to-1** distillation have **no** executable
  chunks and still refuse with `chunkNotImplemented`. The logical-measurement certificate
  is **structural** (observable ↔ flows ↔ QStab readout vars), **not** a stabilizer-flow /
  fault / decoder proof. This is **not** "the complete MagicQ → QStab compiler"; it is a
  verified, honestly-bounded pair of subsets with the rest visibly deferred. Gidney
  full-chunk exactness, decoder performance, and physical lattice-surgery correctness are
  **not** claimed anywhere.

## See also

- [../README.md](../README.md) — the Compiler layer overview.
- [../CONTRACT.md](../CONTRACT.md) — the proved/decide/assumed/missing tiering contract.
- [../../README.md](../../README.md) — the LogicQ repository root.
- The `Gidney/` subfolder ([Gidney/Basic.lean](Gidney/Basic.lean),
  [Gidney/Cultivation.lean](Gidney/Cultivation.lean)) has no separate README; it is
  documented in the table above.
