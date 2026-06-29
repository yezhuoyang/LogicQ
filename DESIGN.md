# LogicQ — Verified Compilation Pipeline (design & plan)

> A "quantum CompCert": a machine-checked compiler in Lean 4 from a chain-complex–typed
> fault-tolerant language down to a physical Clifford+measurement target, reusing the
> [FormalRV](../FormalRV) framework. Every IR level has (a) syntax in BNF form, (b) precise
> semantics, (c) fixed compilation rules, and (d) a semantics-preservation theorem; the
> per-level theorems **compose** into one end-to-end correctness result.

This document is the detailed plan. It is grounded in a survey of the FormalRV codebase
(248k lines / 1092 files) — every "reuse X" below cites a real module/definition.

---

## 0. Locked design decisions

| # | Decision | Choice |
|---|---|---|
| 1 | High-level surface syntax | **Lean-embedded DSL first** (structures + macros, e.g. ChainQ `code … as LiftedProduct { … }`). **Faithful textual parsers now exist at every level** (`Parsing/Basic.lean` + each layer's `Parse.lean`, all `by decide`-tested): the `.lqr` surface front-end (`Compiler/Surface/Parse.lean`) and OpenQASM (`Compiler/QASM/Parse.lean`) parse **and compile** to Mixed IR; PPM/PPR/QStab/QClifford have total text→AST parsers. Remaining surface features (adaptive PPM control flow, richer `.lqr` code families) are the next increment. |
| 2 | Fault-tolerance scope | **Correctness up to named obligations** — semantics preservation is *proven* through all levels; decoder correctness, code distance, and magic-state physics are *explicit named hypotheses* (FormalRV's `VerifiedShorOnCode` discipline), never silent `sorry`. |
| 3 | Relationship to FormalRV | **Vendor** the minimal needed FormalRV modules into LogicQ (self-contained repo, no external dependency). |
| 4 | Middle-of-pipeline shape | **Linear** `PPM → LatticeSurgery → QStab → QClifford` (PPM statements are *realized by* surgery; one `realizes_trans` fold). |

---

## 1. Headline finding

FormalRV already supplies **~80%** of the stack, and — crucially — most levels exist *with
sorry-free semantics and correctness theorems*. The genuinely new work is concentrated in:

1. **The chain-complex typed front-end** (`ChainQ`): the `CellComplex over Z2` / `StabilizerCode`
   type system, the logical instruction layer (`LogicH`, `LogicCNOT`, `LogicMeasure`, …), and the
   `MagicQ` post-selection sublanguage. No cell-complex / boundary-operator infrastructure exists
   in FormalRV today.
2. **The QStab IR as a first-class language** (`Prop[r,s] P`, `Parity c…`). The *semantics* already
   exists (a `Prop` is a Gottesman measurement = `PPMStmt.measure`; `Parity` is the XOR machinery),
   but the named IR with `[r,s]` scheduling coordinates does not.
3. **The CompCert-style composition spine.** FormalRV's `Framework/Contracts` is about *error-rate
   bounds* (`cycle_logical_error_rate ≤ f_code`), **not** semantics preservation — and it has no
   cross-pass transitivity lemma. LogicQ supplies one uniform refinement relation and a single
   composition theorem.

---

## 2. The pipeline

Six levels. For each: role · BNF · semantics · compile rule out · the correctness theorem on that edge.
**EXISTS** = reuse a FormalRV definition/theorem essentially verbatim; **NEW** = LogicQ builds it.

```
  ChainQ  ──elab──►  PPR  ──sched──►  PPR  ──lower──►  PPM  ──realize──►  LS  ──emit──►  QStab  ──extract──►  QClifford
 (L_FE)             (L_PPR)                          (L_PPM)            (L_LS)          (L_QStab)            (L_QCliff)
   NEW             EXISTS                            EXISTS             EXISTS            NEW                 EXISTS
```

### L_FE — ChainQ (typed chain-complex / stabilizer front-end + MagicQ)  — **NEW**
- **Role.** User-facing typed logical language. QEC codes are values of a chain-complex / CSS /
  stabilizer type over Z2; logical FT operations are typed instructions over indexed code blocks;
  `MagicQ` expresses post-selected `Repeat…Until` protocols / factories.
- **BNF (core; the embedded-DSL surface elaborates to this).**
  ```
  CodeDecl  ::= 'code' Id Params 'as' CodeKind '{' Body '}'
  CodeKind  ::= 'CellComplex' 'over' 'Z2' | 'StabilizerCode' | 'CSSCode'
  CellBody  ::= 'cells' '{' CellGroup* '}' 'boundary' '{' BdyEqn* '}'
                'css' '{' 'hx' '=' MatExpr ';' 'hz' '=' MatExpr ';' '}'
  CellGroup ::= CellSort Id '[' IdxVar* ']' 'in' Range (',' Range)* ';'
  BdyEqn    ::= ('d2'|'d1'|'d0') '(' CellRef ')' '=' BdySum ';'
  BdySum    ::= CellRef ('+' CellRef)*            -- formal Z2 sum
  MatExpr   ::= 'matrix' '(' ('d2'|'d1'|'d0') ')' | 'transpose' '(' MatExpr ')'
  StabBody  ::= ('n' '=' Nat ';')? 'generators' '{' (Id '=' PauliLit ';')* '}'
                ('logical_z' '{' (Id '=' PauliLit ';')* '}')?
  Prog      ::= Decl*
  Decl      ::= CodeKind Id '[' KV* ']'                      -- surface q1 [n=40,k=1,d=5]
              | CVar '=' LogicOp | 'InjectT' QubitRef ',' Handle | Handle '=' ProtocolCall
  LogicOp   ::= 'LogicH' QubitRef | 'LogicCNOT' QubitRef ',' QubitRef
              | 'LogicS' QubitRef | 'LogicT' QubitRef
              | 'LogicMeasure' QubitRef | 'LogicProp' PauliLit
  Protocol  ::= 'protocol' Id '(' Param* ')' ':' 'Repeat' ':' Stmt*
                'Success' '=' BoolExpr 'Until' 'Success' 'return' Handle?
  PauliLit  ::= ('I'|'X'|'Y'|'Z')+
  ```
- **Semantics.** *Static:* a `CodeDecl` denotes a `CSSCode` (`hx := matrix(d2)`,
  `hz := transpose(matrix(d1))`) or `StabilizerCode`; well-typed ⟺ `css_condition` (CSS) / pairwise
  commuting checks (stabilizer), and every declared logical operator yields a valid `LogicalBasis`.
  The chain-complex law `∂₁∘∂₂ = 0` over Z2 is exactly what forces `Hx·Hzᵀ = 0`. *Dynamic:* a `Prog`
  denotes a logical channel — the elaborated PPR program under `RotProg.denote`, decoded onto the
  code's logical subspace. `MagicQ Repeat…Until` denotes a **post-selected channel** (the state
  conditioned on `Success`) with a counted attempt budget.
- **Reuse.** `CSSCode` + `css_condition` + `syndrome_circuit_implements_code`
  (`QEC/CSSCode.lean`); `StabilizerCode` + `code513_valid` (`QEC/StabilizerCode.lean`);
  `LogicalBasis` + validity + `valid_logical_not_Zstabilizer` (`QEC/Logical*.lean`); the algebraic
  CSS builders (`QEC/FrontendAlgebraic.lean`: `hypergraphProduct`, `surfaceHGP`, `bivariateBicycle`,
  `liftedProduct`); `PauliProduct`/`PauliString` for `PauliLit`; `TFactory` +
  `factory_tGate_correct` for protocol factories.
- **NEW.** Z2 cell-complex type (`CellSort`, indexed cells, boundary operators `d0/d1/d2` as formal
  Z2 sums) and its elaboration to `BoolMat hx/hz`; the proof generator `∂∂=0 ⟹ css_condition`;
  the embedded-DSL macro layer + decidable type checker; the `MagicQ` protocol AST + post-selected
  channel denotation; decidable logical-op typing rules.
- **Compile out.** `elabChainQ : ChainQ.Prog → PPR.RotProg`. Logical gates → their fixed Litinski
  rotation expansion (a dictionary modeled on `PauliRotation/Compiler/GateBridge.lean`'s `gateRots`,
  retargeted to logical Paulis); `LogicMeasure` → terminal π/2 readout rotation tagged for PPM
  measurement; `InjectT`/`Distill` → a `useT`/`useCCZ`-tagged rotation sourced from the elaborated
  `TFactory`.
- **Correctness theorem.** `elabChainQ_denote` (well-typed `p` ⟹ decoded `RotProg.denote` of the
  elaboration equals `logicalSem p`); `chainComplex_css` (`∂₁∘∂₂=0 ⟹ css_condition`); MagicQ
  `protocol_factory_correct` (a `Success`-accepting run lands in the +1 eigenspace of the target
  magic stabilizer — T case via `hXY_stabilizes_magicT`).

### L_PPR — Pauli-Product Rotation IR  — **EXISTS (reuse verbatim)**
- **Role.** Litinski rotation layer: logical instructions as `e^{-iθP}` with `θ ∈ ±{π,π/2,π/4,π/8}`,
  grouped into parallel commuting layers; `countPi8` = T-count.
- **BNF.** `RAngle ::= 'pi'|'piHalf'|'piQuarter'|'piEighth'`; `Rot ::= '<' neg ',' RAngle ',' PauliProduct '>'`;
  `RotLayer ::= Rot*` (axes pairwise commute — a wf side condition, not grammar); `RotProg ::= RotLayer*`.
- **Semantics.** Denotational over involutive matrices (no exponential series):
  `rotOf θ M = cosθ·I − i·sinθ·M` for `M²=I`; layer product over commuting rotations; program =
  right-to-left layer composition. Sorry-free in FormalRV.
- **Reuse.** `PauliRotation/Syntax.lean` + `Semantics/{Core,CommBridge,PauliPhase,BasisAction}.lean`
  (`rotOf`, `axisMat`, `rotOf_mul_same/cancel/comm`, `axisMat_comm_of_commF`) +
  `Compiler/Scheduler.lean` (`scheduleList`, `scheduleList_denote`).
- **Compile out.** (1) `scheduleList : List Rot → RotProg` (ASAP, denotation-exact). (2)
  `lowerFlat`/`lowerRot : RotProg → PPMProg` (π→`frame`; π/4→S-block 2 measurements; π/8→T-block
  with `measureSel` + `useT`). A thin NEW wrapper folds `lowerFlat` over layers.
- **Correctness theorem.** `scheduleList_denote` (EXISTS, exact) and `lowerFlat_magicT`
  (`countMagicT = countPi8`, EXISTS); `lowerProg_denote` (NEW thin assembly from existing branch
  denotations).
- **Inherited open item.** The `gateRots` *dictionary leg* — that the chosen rotation expansion of
  each gate equals its unitary — is the one acknowledged-open FormalRV item; LogicQ must discharge
  it for the logical `{H,S,T,CNOT}` set (see Risks).

### L_PPM — Pauli-Product Measurement IR  — **EXISTS (reuse verbatim)**
- **Role.** Measurement-based logical IR: outcome-binding Pauli measurements, adaptive
  selective-destruction, Pauli-frame corrections, magic injection.
- **BNF.**
  ```
  PauliProduct ::= PFactor*                                  (sortedStrict)
  PPMStmt ::= 'measure' CVar PauliProduct
            | 'measureSel'  '[' CVar* ']' CVar P P
            | 'measureSel2' '[' CVar* ']' '[' CVar* ']' CVar P P P P
            | 'frame' PauliProduct
            | 'correct' '[' CVar* ']' PauliProduct PauliProduct
            | 'useT' Nat | 'useCCZ' Nat Nat Nat
  PPMProg ::= PPMStmt*    (wf: sequential outcome binding, sortedStrict, bound-slot refs)
  ```
- **Semantics.** Operational (Gottesman/Heisenberg): `run` evolves a `StabilizerState` via
  `apply_PPM_pos/neg`, threading an outcome stream, a deferred Pauli frame, and magic counters.
  Denotational (per outcome branch): `progDenote` with projectors `pauliProj(P,b)=(I+(-1)^b P)/2`.
- **Reuse (gold standard).** `PPM/Syntax/Program.lean` (clean zero-import leaf IR, decidable `wf`,
  structural laws) + `Semantics/{ProgramSemantics,PPMDenote,PPMOperational}.lean`
  (`run`, `run_append`, `run_magicT/CCZ`, PVM laws) + `Compiler/{PPMCompilerCorrectness,
  StabProgram}.lean` (**`RealizesUpToFrame`**, `realizes_comp`, `compileToPPM_correct`,
  `PPMGadgetInterface`, H/CNOT truth tables).
- **Compile out (linear, per decision #4).** Each logical-Pauli `measure` statement →
  a `SurgeryGadget`/weld; `useT`/`useCCZ` → factory port + teleport gadget; `correct` → Pauli-frame
  ops. Threads the deferred frame.
- **Correctness theorem.** `ppmStmt_realized_by_surgery` (NEW) from
  `surgery_implements_logical_measurement` (EXISTS); program lift via `run_append` + `chainOK_sound`.

### L_LS — Lattice Surgery IR  — **EXISTS (reuse verbatim)**
- **Role.** Spacetime realization of multi-patch logical Pauli measurements as patch merges/splits
  on a 3D pipe diagram; long-range routing via ancilla highways.
- **BNF.** `LaSre` (a record of `Nat→Nat→Nat→Bool` planes) + `Corr`/`Surf`/`Port`; `LSProgram` =
  weld-tree `Gadget | weldK L R | weldI L R | rotLaS L`; `Gadget = SurgeryGadget {target_pauli,
  merged_hx, merged_hz, span_witness}`.
- **Semantics.** Denotational via correlation-surface validity (`valid`/`funcOK → LaSCorrectFull`);
  operational bridge `measureChecks` mapping a merge to the merged stabilizer group.
- **Reuse.** `QEC/LatticeSurgery/{LaSre,Weld,RoutedMerge,SurgeryCorrect,SurgerySchedule,
  ChainComposition}.lean`: `surgery_implements_logical_measurement`,
  `surgery_preserves_commuting_logical`, `schedule_runs_as_surgeries`, `chainOK_sound`, `block_correct`.
- **Compile out.** Each merge/split + its syndrome schedule → QStab `Prop[r,s]`/`Parity`: a merge
  over rounds `r=0..d-1` emits `Prop[r,s]` of the merged-code stabilizers; `Parity` nodes combine
  outcomes across rounds. Reuse the round/decode threading shape of
  `System/Compile/QECScheduleToSystem.lean`.
- **Correctness theorem.** `ls_to_qstab_sound` (NEW) from `schedule_runs_as_surgeries` (EXISTS) +
  `run_append`.
- **Inherited scaling gap.** No inductive `weldK`-preserves-`LaSCorrectFull` theorem; whole-program
  verification uses **per-interface `chainOK_sound` (O(N))** rather than `native_decide` (exponential).

### L_QStab — physical stabilizer-measurement program  — **NEW IR (semantics exists)**
- **Role.** Physical-qubit-level program of timed Pauli-product measurements and classical parity
  combinations (the README's `c0 = Prop[r=0,s=0] ZZI; d0 = Parity c0 c2; o0 = Parity c4`).
- **BNF.**
  ```
  QStabStmt ::= CVar '=' 'Prop' ('[' 'r' '=' Nat ',' 's' '=' Nat ']')? PauliLit
              | CVar '=' 'Parity' CVar+
  QStabProg ::= QStabStmt*
  ```
- **Semantics.** Operational: each `Prop` is a Gottesman measurement on the **physical**
  `StabilizerState`; `r,s` are scheduling coordinates (round, parallel slot) constraining the
  schedule; `Parity` is classical XOR over bound outcome bits; outputs `o*` are decoded logical bits.
- **Reuse.** `Prop` = `PPMStmt.measure`; `Parity` = `correct`'s XOR-parity machinery +
  `run_outs_length` accounting (`PPM/Semantics/ProgramSemantics.lean`).
- **NEW.** The QStab inductive (`Prop` with optional `[r,s]`, `Parity` over `CVar`s) + `wf`; the
  erasure bridge `QStab → PPMProg` proven to preserve `run`; the `[r,s] → SpaceTimeInvariant`
  scheduling constraint (reuse `System/Invariants/InvariantFramework.lean`).
- **Correctness theorem.** `qstab_to_qclifford_sound` (NEW): Gottesman denotation of a `QStabProg`
  equals the stabilizer evolution induced by the emitted QClifford circuit's measurements
  (composed via `run_append`).

### L_QCliff — physical Clifford+measurement circuit (target)  — **EXISTS (thin wrapper)**
- **Role.** The executable artifact: physical Clifford gates (H,S,CNOT/CZ) + computational
  measurements + classically-conditioned Pauli corrections.
- **BNF.** `QCStmt ::= 'H' q | 'S' q | 'X' q | 'Z' q | 'CNOT' c t | 'CZ' a b | 'Meas' q '->' CVar |
  'If' BoolExpr 'then' Pauli q`; `QCliff ::= QCStmt*` (maps onto FormalRV `BaseCom`).
- **Semantics.** Via FormalRV `Core`: Clifford fragment through `uc_eval : BaseUCom → Square dim`
  (`UnitarySem.lean`); measurement + conditionals through `c_eval : BaseCom → Superoperator`
  (`DensitySem.lean`); resources via `Gate.tcount/gcount/depth`.
- **Reuse.** `Core/{Gate,QuantumGate,UnitarySem,DensitySem,GateDecompositions}.lean`
  (`uc_eval`, `pad_u`/`pad_ctrl`, `c_eval`, `X_X_id`/`H_H_id`/`Rz_Rz_add`,
  `uc_eval_unitary_of_wellTyped`).
- **NEW (thin).** `QClifford` inductive + erasure to `BaseCom` (definitional).
- **Correctness theorem.** `qstab_prop_extracts` (NEW) from
  `extractionRound_measures_code` (`QEC/Circuit/CircuitSemantics.lean`, EXISTS) + `qcliff_denote_def`.
  This is the **bottom** of the chain.

---

## 3. Correctness strategy (the CompCert analogue)

**One uniform simulation relation.** Each pass `compile_i : IR_i → IR_{i+1}` is certified by a
theorem of the canonical FormalRV shape

```
RealizesUpToFrame (sem_{i+1} (compile_i p)) (frame_i p) (sem_i p)        -- "op = frame · spec"
```

— "realizes the spec up to a *deferred Pauli frame*." (def: `PPM/Compiler/PPMCompilerCorrectness.lean`.)
For the unitary/rotation levels (FE→PPR→PPM) `sem` is the matrix denotation
(`RotProg.denote`/`progDenote`); for the stabilizer levels (PPM→LS→QStab→QClifford) `sem` is the
Gottesman `run` and the relation is "same stabilizer change / measured logical, with byproduct
Paulis collected into the frame." Choosing `RealizesUpToFrame` **uniformly** is the key decision:
it is closed under composition and FormalRV already proves the composition lemma `realizes_comp`.

**Per-pass theorems (one per edge).**

| Edge | Theorem | From |
|---|---|---|
| FE→PPR | `elabChainQ_denote` (NEW) | discharges `gateRots` dictionary leg for {H,S,T,CNOT}, reuses `rotOf` algebra |
| PPR→PPR (sched) | `scheduleList_denote` (EXISTS, exact) | `PauliRotation/Compiler/Scheduler.lean` |
| PPR→PPM | `lowerProg_denote` (NEW thin) | `lowerRot` branch denotations + `lowerFlat_magicT` |
| PPM→LS | `ppmStmt_realized_by_surgery` (NEW) | `surgery_implements_logical_measurement` (EXISTS) |
| LS→QStab | `ls_to_qstab_sound` (NEW) | `schedule_runs_as_surgeries` (EXISTS) + `run_append` |
| QStab→QClifford | `qstab_prop_extracts` (NEW) | `extractionRound_measures_code` (EXISTS) + `qcliff_denote_def` |

**Composition.** FormalRV has no cross-pass transitivity lemma; LogicQ supplies it **once**:

```
realizes_trans : RealizesUpToFrame op f₁ (sem_{i+1} q)
               → RealizesUpToFrame (sem_{i+1} q) f₂ (sem_i p)
               → (frame-conjugation side condition)
               → RealizesUpToFrame op (f₁ · f₂') (sem_i p)
```

This lifts `realizes_comp` to the pass level (frames accumulate by the Heisenberg rule
`U₂·f₁ = f₁'·U₂`). End-to-end `LogicQ_pipeline_correct` is a **5-fold `realizes_trans`** over the six
levels, terminating at `c_eval` of the emitted QClifford circuit:

> the emitted physical Clifford+measurement circuit realizes the logical channel of the source
> `ChainQ` program, up to a classically-tracked Pauli frame and code decoding, **assuming** the
> named decoder/distance/magic-physics obligations.

**Resource chain (parallel).** `countPi8` (PPR) = `countMagicT` (PPM) = magic ports (LS) = T-factory
volume (QClifford), each an existing theorem; `CostModel` instances feed
`estimateWith_time/qubits` (proven ∀ m). MagicQ `Repeat…Until` is bounded by
`SymbolicRepeatSoundness` — **no loop unrolling**.

**Honesty gate.** Every per-pass theorem and `LogicQ_pipeline_correct` are guarded by
**`#verify_clean`** (`Verifier/ProofGate.lean`; axioms ⊆ {propext, Classical.choice, Quot.sound}).
Open physics is a `VerifiedLogicQProgram` structure of **named, non-vacuous obligation fields**
(decoder, distance, magic physics) — never `:= True`, never silent.

---

## 4. Packaging & vendoring (decision #3)

LogicQ is a **self-contained Lake package** that vendors the minimal FormalRV closure.

**Vendoring is bounded** (measured): importing FormalRV *umbrellas* drags in all of Arithmetic(142)
+ Shor(38) ⇒ 382 modules / ~108k lines. Importing the **precise leaf modules** instead:

| Closure | modules | ~lines | dominated by |
|---|---:|---:|---|
| P1 minimal vertical slice | 130 | 36.8k | QEC 57, Core 22, PauliRotation 18, PPM 17 |
| Full (P1 + front-end + magic + framework) | **137** | **37.6k** | QEC 62, Core 22, PauliRotation 18, PPM 17, Framework 6 |

Only **4 small Arithmetic utility modules** remain (pulled by `PauliRotation/Semantics/BasisAction`
→ `Arithmetic.Correctness`). **Rule: vendor leaf modules, never umbrellas.**

**Layout** (vendored subtree keeps `FormalRV.*` module names + imports unchanged so it compiles as-is;
LogicQ's own code lives under the existing top-level dirs):

```
LogicQ/
  lakefile.toml          lean-toolchain   LogicQ.lean (umbrella)   README.md   DESIGN.md
  FormalRV/              ← vendored 137-module closure (namespaces/imports unchanged)
  Prelude.lean           ← single import shim re-exporting the stable FormalRV surface
  Type/                  ← L_FE: Syntax, Elab, Semantics, MagicQ                       [NEW]
  PPR/                   ← thin re-exports of FormalRV.PauliRotation                    [reuse]
  PPM/                   ← thin re-exports of FormalRV.PPM                              [reuse]
  LatticeSurgery/        ← thin re-exports of FormalRV.QEC.LatticeSurgery               [reuse]
  QStab/                 ← Syntax, Semantics                                            [NEW]
  QClifford/             ← Syntax (BaseCom erasure)                                     [NEW]
  Compiler/              ← FEtoPPR, PPRtoPPM, PPMtoLS, LStoQStab, QStabtoQClifford,
                            EndToEnd (realizes_trans + LogicQ_pipeline_correct)         [NEW]
  Library/               ← surface(d) family, README examples as #verify_clean demos    [NEW]
  Verifier/Spec.lean     ← VerifiedLogicQProgram contract + named obligations           [NEW]
```

**Build discipline (inherited from FormalRV; mandatory).**
- Toolchain pinned: `leanprover/lean4:v4.29.1`; mathlib `git#v4.29.1` (must match the vendored code).
- `lake exe cache get` for mathlib oleans before first build.
- **Always `lake build -j 1`** with `moreLeanArgs = ["-M","8000"]` — 12 workers × multi-GB ⇒ OOM on
  this machine. Keep files small/topical so no worker approaches the 8 GB cap.
- Heaviest expected files (`Compiler/EndToEnd.lean`, `Library/Examples.lean`) stay small by using
  per-gadget `chainOK_sound` certificates instead of whole-program `native_decide`.

*Note:* the mathlib-heavy cost concentrates in `Core` matrix semantics (`uc_eval`, `Square dim`),
pulled in by PPR's complex-matrix `rotOf`. The stabilizer levels (PPM/LS/QStab) are pure
`Bool`/`List`/`Nat` and cheap.

---

## 5. Phased roadmap

**Methodology — languages first (per the project owner's directive).** Each IR level's
*syntax + type system + semantics* is fixed as an independent, self-contained, sorry-free Lean
specification **before** any inter-level compiler pass is built. The spec phase is authored cleanly
in LogicQ (semantic rules small enough to state directly) and kept **Mathlib-free** wherever the
level is pure `Bool`/`List`/`Nat` (front-end type system, PPM, QStab); FormalRV is vendored and
reused for the heavy *correctness proofs* only in the later compiler phase. Mathlib enters only for
the analytic PPR/QClifford complex-matrix denotations.

### 5a. Spec phase — define each level independently (CURRENT)

| Phase | Level | Deliverable | Status |
|---|---|---|---|
| **S0** | Package | `lakefile.toml` (Mathlib-free, `-M 8000`), `lean-toolchain` v4.29.1, `LogicQ.lean` umbrella, building with `lake build` | ✅ done |
| **S1** | ChainQ type system | `LogicQ/ChainQ/{GF2,Code,ChainComplex}.lean`: GF(2) algebra; `CSSCode`/`StabilizerCode` + decidable validity; the chain complex over Z2 + `chainLaw` (∂∂=0) + `toCSS`; **`chainComplex_css`** (type-system soundness); worked surface patches + five-qubit code type-check by `decide` | ✅ done |
| **S3** | PPM = QMeas syntax+semantics | `LogicQ/PPM/{Syntax,Semantics}.lean`: the **QMeas** measurement-based language — `meas`, **adaptive `if r=+1 then…else…`**, `for`, `frame_P` (composing), `discard`, `abort`, `seq`/`skip`; full small-step operational semantics (all rules), multi-step closure + `trans`, `abort` stuck-terminal + accepted/rejected partition; the **H-gadget frame table proven for all 4 outcome branches** from the rules; post-selection `checkPlus` accept/reject. Mathlib-free; quantum state parametric (`QInterp`). | ✅ done |
| **S2** | PPR syntax + semantics | `PPR/Syntax.lean`: `Rot = Phase × PauliString` (`exp(i φ P)`), `Phase = ±{π,π/2,π/4,π/8}`, `PauliString = List (LQubit × Pauli)` over **logical** qubits, `tCount` (= π/8 count). `PPR/Semantics.lean` (**first Mathlib module**): **`rotOf φ M = cos φ·1 + i·sin φ·M`**; a Pauli string denotes a monomial `Matrix (Fin n → Bool) … ℂ` (no Kronecker), via a layout `lay : LQubit → Fin n`; `Rot.denote`/`RotProg.denote` (= matrix product); laws `rotOf_zero`, `denote_nil/singleton`, and **`denote_append : denote (p++q) = denote q * denote p`**. | ✅ done |
| **S0b** | Shared `Logical` vocabulary | `Logical.lean`: `BlockId`, `LQubit = ⟨blk,idx⟩` — the logical-qubit addressing shared by ChainQ/PPR/PPM (PPM rewired to it). | ✅ done |
| **S0c** | Shared `Physical` vocabulary | `Physical.lean`: `PQubit`, 4-element `Pauli` (`I,X,Y,Z`), dense-string `ofString` ("ZZI"). The physical analogue of `Logical`. | ✅ done |
| **S5** | QStab syntax+semantics | `QStab/{Syntax,Semantics}.lean`: `Prop[r,s] P` / `Parity c…` SSA dataflow + `wf`; the **classical syndrome/readout `eval`** (prop = outcome, parity = XOR) over `Bool` + `eval_length`; README `progReadout` (d=3 readout) evaluated by `decide`. (Physical Gottesman back-action is the same parametric `proj` hook, deferred.) | ✅ done |
| **S6** | QClifford spec | `QClifford/{Syntax,Semantics}.lean`: Clifford + `Meas q->r` + `If r then P q` circuit; resource readouts (`width`/`gateCount`/`twoQubitCount`/`measCount`); a **parametric operational semantics** (`Host St` + `run`) with **`run_append`** composition law; `cnotFromCZ` example. (Concrete `Host` = stabilizer tableau / FormalRV `uc_eval`, deferred.) | ✅ done |
| **S4** | LatticeSurgery spec | `LatticeSurgery/{Syntax,Semantics}.lean`: surgery IR + merge/`measureChecks` semantics | next |

### 5b. Compiler phase — compile between the fixed levels (LATER)

Only after all six languages are pinned do we build and verify the passes. Each milestone ends in a
`#verify_clean`-gated artifact.

| Phase | Goal | Deliverable | Reuses |
|---|---|---|---|
| **P0** Scaffold | Stand up the package + import boundary | `lakefile.toml`, `lean-toolchain`, vendored `FormalRV/` closure, `LogicQ.lean`, `Prelude.lean`; one `#verify_clean` theorem reusing an imported lemma (e.g. `rotOf_mul_same`) | — |
| **P1** Vertical Clifford slice | End-to-end `RealizesUpToFrame` for a hand-written PPR prog through PPM→LS→QStab→QClifford on one CNOT | `lowerProg_denote`, `ppmStmt_realized_by_surgery`(CNOT), `ls_to_qstab_sound`, `qstab_prop_extracts`, **`realizes_trans`**, composed `LogicQ_cnot_realized` | `scheduleList_denote`, `lowerFlat`, `surgery_implements_logical_measurement`, `realizes_comp`, `extractionRound_measures_code` |
| **P2** Chain-complex front-end (static) | Elaborate `surface(d)` + `five_qubit` to codes; prove well-typedness | `Type/{Syntax,Elab,Semantics}.lean`; `chainComplex_css` wired to `syndrome_circuit_implements_code` | `CSSCode`, `css_condition`, `StabilizerCode`, `LogicalBasis`, `FrontendAlgebraic` |
| **P3** FE→PPR dictionary | Elaborate logical {H,S,T,CNOT,Measure,Prop} → PPR; discharge the dictionary leg | `Compiler/FEtoPPR.lean` + `elabChainQ_denote`; the q1/q2 program (minus magic) compiles to a verified `RotProg` | `gateRots` shape, `rotOf` algebra, P2 code context |
| **P4** MagicQ + injection | `Distill15to1_T` → `TFactory`; verify `InjectT` | `Type/MagicQ.lean`; `protocol_factory_correct` (T via `hXY_stabilizes_magicT`) + attempt-budget bound | `TFactoryCircuit`, `factory_tGate_correct`, `ctrlHXY_check_passes`, `SymbolicRepeatSoundness` |
| **P5** Full end-to-end | Compose all six passes for the full README program; resource chain + contracts | `Compiler/EndToEnd.lean` `LogicQ_pipeline_correct` (5-fold `realizes_trans`); resource chain; `CostModel` bounds; `VerifiedLogicQProgram`; `Library/Examples.lean` all `#verify_clean` | `realizes_comp`, `CostModel`/`estimateWith`, `Contracts` freeze pattern, `ProofGate` |

---

## 6. Risks

1. **`gateRots` dictionary leg** (rotation expansion = gate unitary) is FormalRV's one open
   Pauli-rotation item; LogicQ's FE→PPR theorem (P3) inherits it for logical {H,S,T,CNOT}.
2. **Chain-complex math is entirely new** — the Z2 cell-complex type, boundary-matrix evaluation,
   and `∂∂=0 ⟹ css_condition` are the riskiest novel content (front-end).
3. **Lattice-surgery scaling** — no inductive `weldK`-preservation theorem; must adopt per-interface
   `chainOK_sound` (O(N)) from day one or large programs are unverifiable (`native_decide` blows up).
4. **PPM outcome generality** — `apply_PPM_outcome_independent_ops` is proven only for H/CNOT;
   generalizing deferred-frame independence to arbitrary gadgets is an open obligation the
   composition silently depends on.
5. **QStab is genuinely new** — first-class `[r,s]` timing + the denotation-equals-PPM-run bridge is
   more than "reuse."
6. **FT facts assumed** — distance, decoder, magic-state physics are named obligations, not proven
   (per decision #2); the end-to-end claim is "correct up to" them.
7. **Vendoring drift** — the vendored closure is a point-in-time copy; FormalRV improvements (e.g.
   closing the dictionary leg) must be re-pulled manually. Record the source FormalRV commit.
8. **Core `DensitySem`/`NDSem`** measurement-commutativity proofs are scaffolded; off the critical
   path for Clifford-only feedforward, but a hazard if QClifford correctness needs more.

---

## 7. Reuse inventory (load-bearing FormalRV anchors)

- `PPM/Syntax/Program.lean` — `PKind`/`PFactor`/`PauliProduct`/`PPMStmt`/`PPMProg` + decidable `wf`
  (the universal Pauli-axis type for **all** levels; do not redefine).
- `PauliRotation/{Syntax,Semantics/*,Compiler/Scheduler,Compiler/ToPPM/Lowering}.lean` — PPR IR +
  `rotOf` algebra + `scheduleList_denote` + `lowerFlat_magicT`.
- `PPM/Compiler/PPMCompilerCorrectness.lean` — **`RealizesUpToFrame` + `realizes_comp`** (the frame
  spine and composition lemma).
- `PPM/Semantics/{ProgramSemantics,PPMOperational,PPMDenote}.lean` — Gottesman `run`, `run_append`,
  PVM laws.
- `QEC/CSSCode.lean` + `FrontendAlgebraic.lean` — `CSSCode`, `css_condition`, `toStabilizers`,
  `syndrome_circuit_implements_code`, the HGP/BB/LP/surface builders.
- `QEC/{StabilizerCode,Logical,LogicalMeasurementGeneral}.lean` — stabilizer codes, `LogicalBasis`,
  `valid_logical_not_Zstabilizer`.
- `QEC/LatticeSurgery/*` — `LaSre`, welds, `surgery_implements_logical_measurement`, `chainOK_sound`,
  `schedule_runs_as_surgeries`.
- `QEC/Cultivation/*` + `PPM/Compiler/ToffoliScheme.lean` — `TFactory`, `factory_tGate_correct`,
  `hXY_stabilizes_magicT`.
- `QEC/Circuit/CircuitSemantics.lean` — `extractionRound_measures_code`.
- `Core/{Gate,QuantumGate,UnitarySem,DensitySem,GateDecompositions}.lean` — `uc_eval`, `c_eval`,
  Clifford identities (ground-truth target semantics).
- `Framework/{Contracts,CostModel,ResourceEstimate}.lean` + `System/Invariants/InvariantFramework.lean`
  + `System/Artifacts/CompressedRepeat/SymbolicRepeatSoundness.lean` — contract freeze, cost models,
  loop-free repeat soundness.
- `Verifier/ProofGate.lean` — `#verify_clean` / `#verify_rejects`.

---

*Survey + synthesis basis: a 10-agent parallel read of FormalRV (Core, PPR, PPM, QEC/chain-complex,
Lattice Surgery, Framework contracts, all existing compile passes, the high-level/QStab layer,
planning docs, packaging), validated against direct reads of `Framework/Contracts.lean`,
`PPM/Syntax/Program.lean`, `PPM/Compiler/StabProgram.lean`, `QEC/FrontendAlgebraic.lean`, and a
computed import-closure measurement.*
