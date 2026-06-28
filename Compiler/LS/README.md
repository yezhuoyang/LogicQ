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

## Example

```lean
-- a 2-body `ZZ` is a well-formed measurement; its dense form on 3 qubits is `ZIZ`/`ZZI`:
example : SPauli.wfMeas [(0, .Z), (1, .Z)] = true := by decide
example : SPauli.toDense 3 [(0, .Z), (2, .Z)] = ofString "ZIZ" := by decide
-- an identity factor is rejected, a duplicate qubit is rejected, an empty measurement is rejected:
example : SPauli.wf [(0, .I)] = false := by decide
example : SPauli.wf [(0, .Z), (0, .X)] = false := by decide
example : SPauli.wfMeas ([] : SPauli) = false := by decide
-- an out-of-range factor is caught by `inRange`:
example : SPauli.inRange 2 [(0, .Z), (5, .Z)] = false := by decide
```

These `by decide` tests ([Syntax.lean](Syntax.lean), lines 64-71) pin down the
sparse-Pauli well-formedness discipline: a measurement must be non-empty, free of
identity factors and duplicate qubits, and in range, and it densifies to the expected
`QStab.PauliString`.

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
