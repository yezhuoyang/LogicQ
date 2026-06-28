# LogicQ compiler contract (M23)

> M23 update: `Compiler.QStab2QClifford` is no longer an empty stub.  It lowers
> QStab `Prop`/`Parity` dataflow to QClifford with a per-`Prop` extraction scheme —
> **standard X/Z, destructive readout, Shor (cat+verifier), Knill (transversal),
> `flagX`, and `flag2X`** (X-type flag schemes only — no `flagZ`/`flag2Z`).  It is a
> **normalized LeanQEC port**: each gadget's quantum plumbing is kept faithful but its
> `measZ`s are factored into the generic measurement loop + one classical `parity`
> (proved identical for the trace; informally real-host-equivalent on disjoint qubits,
> NOT proved), NOT a byte-for-byte copy.  Helpers (ancilla/cat/verifier/flags) must
> live **outside the data register
> `[0, P.length)`** (`extractionSpecOk`; the M23 review fix — rules out aliasing a
> data qubit even when it is identity in `P`).  Proven (trace-host **classical
> dataflow** only): `compile?_trace_correct` (compiled store = extraction-local SSA
> dataflow), `propStoreUpdate_resultVar` (each prop's result var = its syndrome), and
> the **source-semantics bridge** `compile?_trace_evalVar` (the compiled store agrees
> with `QStab.evalVar` on every source variable, under the extraction-induced outcome
> stream).  NOT proven here: fault tolerance, distance, hook detection, verifier/flag
> weight bounds, and the physical stabilizer channel (LeanQEC's Heisenberg layer).  The
> older M22 paragraph below is superseded only for the `QStab -> QClifford` edge; the
> remaining missing-pass notes still apply to `ChainQ -> PPR`, `PPR -> PPM`, `PPM -> LS`.

**Read this first.** The implemented compiler targets the **Mixed IR**
(`Compiler.MixedInstr`). The linear pipeline `ChainQ → PPR → PPM → LS → QStab →
QClifford` in `DESIGN.md` is the **intended/future** plan: `PPR`, `QStab`, `QClifford`
are *verified standalone language specs* (syntax + semantics + laws, axiom-clean) that
are **only partially wired together** — `Compiler/{ChainQ2PPR, PPM2LS,
QStab2QClifford}` are no longer all empty: QStab2QClifford has a multi-scheme
extraction pass (standard/Shor/Knill/`flagX`/`flag2X`, M23). The **main end-to-end
wired path** is `Source LogicalOp → Mixed IR` (via `compile?`), plus the `Mixed/PPM →
QStab → QClifford` extraction edges (one-measurement skeleton `ppmMeasToQStab` into
QStab; the M23 multi-scheme `QStab2QClifford.compile?` out) and the external/assumed
`CodeSwitch` certificates.

No `sorry`/`admit`/`native_decide` in the `QStab2QClifford` pass or the core
`Source → Mixed` compiler; their soundness theorems are axiom-clean (`propext` /
`Quot.sound`, with `Classical.choice` in the M23 bridge from a `List` lemma).
EXCEPTION: the user-added `Compiler/CodeSwitch/QLDPCPapers/*` modules use `native_decide`
(13 occurrences in `Concrete.lean`/`Verification.lean`, for large concrete BB/toric
instances) — out of the M23 cleanup scope, and now built because the `Compiler.*` glob
includes them.  The `ChainQ2Mixed` layer (`Compile.lean`/`Primitive.lean`) and the
checker definitions it routes through are themselves `native_decide`-free.

### Tier legend
- **P** = proved theorem (∀-quantified, kernel-checked)
- **D** = executable `by decide` test (a specific finite instance)
- **A** = documented assumption (honest deferral; ideal-channel / external / no-Step)
- **M** = missing implementation (named, not built)

## §1. Stage contract matrix

| Stage | Syntax | Checker | Semantics | Pass IN | Pass OUT | Soundness | Completeness | Examples | Deferred |
|---|---|---|---|---|---|---|---|---|---|
| **1 Source** (`LogicalOp`) | `Mixed/Syntax.lean` `LogicalOp` **P** | `Mixed/Source.lean` `sourceWellFormed`/`sourceOpOk`/`srcOpOk`; `Lower/ProgramOk.lean` `ProgramOk` **P** | `LogicalOp.srcAction` (partial) + `Simulator` `opGate?`/`sourceGates` (ideal) **A** | — (top) | `compileOpR→compileProgram→compileProgramLocA→compile?` (`Lower/Public.lean`) | `compile?_sourceOk`, `sourceCompilable_wellFormed` **P** | `ProgramOkSupported_compiles` (H/S, k=1 only) **P** | Demo §1/§5/§8 **D** | `tGate` magic deferred; CNOT/CZ need adapter caps; no parser (Lean DSL) |
| **2 PPR** | `PPR/Syntax.lean` `Rot`/`RotProg` **P** | only `RotProg.wf` (Bool) **M** | denotational `Rot.denote`/`denote_append` **P** | none (`ChainQ→PPR` planned) **M** | none (`PPR→PPM` planned) **M** | none **M** | none **M** | `Syntax.lean` `tCount`/`wf` **D** | ISOLATED island — no compiler consumer |
| **3 PPM** | `PPM/Syntax.lean` `Stmt` + gadgets **P** | `TypeChecker` `checkPPM`/`checkPPMStmt`; Mixed `checkInstr .ppm` **P** | operational `PPM.Step`/`Steps` (parametric `QInterp`) **P** | Source→PPM gadgets in `compileOpR` | `ppmMeasToQStab` (one meas) | `progH_frame`, `progHAt_frame`, `progCZAt_steps`/`progSAt_steps`/`progCNOTAt_steps` (M22, frame-level), `ppm_step_lifts_ppm_semantics` **P** | `compileOp_complete_measure` **P** | `MTarget.wf`, frame table **D** | **gadget CHANNEL** correctness (carrier/`QInterp.proj`) **A**; full progSAt/progCNOTAt *frame tables* **M**; `progCZAt` experimental placeholder **A** |
| **4 Mixed IR** (target) | `Mixed/Syntax.lean` `MixedInstr` (`ppm`/`transversal`/`automorphism`/`switch`/`magic`/`pauli`) **P** | `Mixed/Check.lean` `checkInstr`/`checkLogicalExec` (threads `TypedEnv`+`PPMState`) **P** | operational `Step`/`Steps` (parametric `MixedInterp`) **P** | `compileOpR` (from Source) | `execMixed` (exec); `ppmMeasToQStab`/`CodeSwitch` (bridges) | `compileProgramLocA_sound`, `compileOp_sound`; `Step_implies_checkInstr`, `no_step_magic`, `Step_transversal_realizes`, `Step_pauli_realizes`, `step_pauli_matches_exec` **P** | `compileOp_complete_{measure,hGate,sGate}`, `ProgramOkSupported_compiles` (supported fragment) **P** | Demo §1/§5/§5b/§7/§8/Contract **D** | **resource pool not threaded** through LEGACY `compile?`/`compileProgramLocA` (uses `AncillaSupply`; the `AncillaPool`/`alloc_valid` discipline IS threaded by the named `ChainQ2Mixed` compiler → `poolOut`, just not yet by `compile?`) **M/A**; `magic` has no `Step`; execMixed multi-block transversal is per-qubit realization, not literal `Step` equality |
| **5 Surgery/Adapter** (`LS2QStab`+`CodeSwitch`) | no distinct LS IR (`LatticeSurgery/` empty) **M**; `SurgeryCert`, `CodeSwitch.SwitchProtocolCert`, Mixed `MixedInstr.switch`+`SwitchCert` **P** | `SurgeryCert.check`/`detectorsDeterministic?`, `*.structuralCheck` (shape/claim only); symplectic `checkSwitch` (GF(2)-decided) **P** | none operational (skeleton) **A** | `ppmMeasToQStab` (one meas) | into QStab `Prog` | `checkSwitch_sound`, `checkPPM_merged_sound` **P**; LS2QStab pass-soundness **M** | none **M** | `progZZ`/`certZZ`, `goodSwitch`, `switchRepInstr` (Contract §3) **D** | distance/fault-distance/decoder **A** (all `FaultStatus.deferred`); `claimed*` recorded, not decided; `CodeSwitch` certs EXTERNAL/ASSUMED |
| **6 QStab** | `QStab/Syntax.lean` `Stmt`(prop/parity)/`Prog` **P** | `Prog.wf` + QStab2QClifford schedule checks `extractionSpecOk` **P/D** | classical dataflow `eval`/`evalVar` (`eval_length` **P**) | `ppmMeasToQStab` | `Compiler.QStab2QClifford.compile?` (standard/Shor/Knill/flagX/flag2X; normalized port; helpers ≥ P.length) **P** | `compile?_trace_correct`, `propStoreUpdate_resultVar`, `compile?_trace_evalVar` (bridge to `QStab.evalVar`) **P** | standard X/Z, destructive, Shor X/Z (wt 2/4), Knill, flagX, flag2X; helper-aliasing rejection **D** | `progReadout`, Shor/Knill trace runs, `bridgeProg` (evalVar) **D** | M23: **classical-dataflow only**; FT / verifier-flag bounds / hook detection / quantum channel = deferred (LeanQEC Heisenberg layer) **A**; no Stim/DEM **M** |
| **7 QClifford** | `QClifford/Syntax.lean` `Gate`/`Circuit` incl. prep/parity **P** | resource readouts + imported QStab schedule checks **P/D** | operational `run` over parametric `Host` (`run_append` **P**) | QStab standard/Shor/Knill/flag extraction **P** | — (terminal) | `run_append` + QStab2QClifford trace correctness **P** | multi-scheme extraction dataflow **P/D** | `cnotFromCZ`, Shor/Knill/flag extraction **D** | concrete tableau `Host` and stabilizer-channel theorem **A/M**; real sim is `Compiler/Simulator` on Mixed |

## §2. Wired edges vs. not-yet-wired passes

**Wired (real) edges:**
- `ChainQ source → Mixed input` = `ChainQ2Mixed.elabProgram?` — a named ChainQ program
  (`hGate`/`sGate`/`xGate`/`zGate`/`blockTransversal{H,S}`) elaborates to `(TypedEnv, List
  LogicalOp)` for `compile?`. The per-op PATH choice (`PathChoice`/`Realization`,
  single-logical transversal **guarded** by `singleLogicalBlock`) and the parallel
  SCHEDULE (`compileScheduled?` → layer-preserving `CompiledSchedule`, paper-stratified
  certificate) are first-class and type-checked by construction. SCOPE: classical typing
  soundness only (inherits the Mixed gadget-channel/FT boundary below); `commutingWithAncilla`
  schedules carry a DEFERRED twist-free/logical-ancilla obligation (2503.05003 §6.3); the
  `Schedule → QStab` lowering is DEFERRED (only `scheduleCoords` survive). No ChainQ-source
  syntax yet for CNOT/CZ/`T`/batch/automorphism/code-switch/scheduled-PPM ops.
- `named ChainQ source → Mixed legality` = `ChainQ2Mixed.compileChainQToMixIR?`
  (`Compile.lean`) — a ChainQ-FACING compiler over the checked primitive surface
  (`Primitive.lean`). A `ChainQPrimProgram` (named code decls + `ChainQPrimOp`s) addresses
  code blocks by CODE NAME and logical qubits by LOGICAL NAME; names resolve via the
  existing ChainQ logical-index pipeline. A fixed, auditable rule table (`buildPrim?` /
  `defaultRulesFor`, CODE-DEPENDENT for `H`/`S`, CERT-DEPENDENT for `cnotGate`) maps each
  op to a checked `MixPrim` (`checkInstr` / `compileScheduled?`); the env+loc-threaded fold
  yields a proof-carrying `CompiledMixIR` (`compileGo_sound` / `compileChainQToMixIR?_sound`,
  `propext`-only: every emitted primitive type-checks in sequence; `codeSwitch` is visible to
  later ops). WITNESS-SAFE BOUNDARY: the public `compileChainQToMixIR?` takes
  `List CapabilityWitness` (not raw `List Capability`; the raw-caps body is `private`;
  conversion is internal, after the witness proves provenance), so a >2-body `measure`
  compiles ONLY through a witnessed capability and a raw `.productSurgery` cap can never enter
  through THIS compiler family. (The lower-level `checkPPM` / Mixed-IR `compile?` kernel is
  still raw-caps and kind-agnostic — `CapKind` there is NOT provenance, only an obligation
  selector; the merge ALGEBRA is enforced kind-independently, so it is a labelling, not a
  soundness, gap — see ChainQ2Mixed/README qLDPC "Kernel caveat".) ADDRESSING + RESOURCE DISCIPLINE: a `LocMap` is threaded so a per-qubit PPM
  teleportation gadget RELOCATES its canonical name to an ancilla and later ops resolve to
  the CURRENT carrier (`H(x); measure(x)` measures the relocated carrier, not the discarded
  original); gadget ancillas must be DECLARED with a basis
  (`StrategyConfig.ancillas : List NamedAnc`) and allocated through `AncillaPool.alloc`
  (valid, live, right basis, available, consumed once). Entry disjointness rejects
  data/ancilla aliasing, and block-level transforms poison ancillas in touched blocks.
  `cnotGate` realization is the per-op `StrategyConfig.cnotMode`: default
  `preferTransversalWithPPMFallback` tries `transversalCNOT` (when a `cnotIncidence` is
  supplied) then FALLS BACK to the PPM gadget — so a valid PPM CNOT is not rejected merely
  because a global incidence is present; `strictTransversal` requires the transversal (no
  fallback), `ppmOnly` forces the gadget. The final pool is preserved in
  `CompiledMixIR.poolOut` (consumed/discarded/available status, queryable). The 10 `MixPrim`
  constructors are all GENUINELY kernel-checked (`ppm` = sugar for `ppmFragment (.meas …)`).
  **DR5 soundness fix:** the prior `homomorphicCNOT`/`gppm` primitives (backed by a weak
  Γ-binding that accepted a dimension-correct ZERO map) were REMOVED. The VERIFIED
  homomorphic CNOT is now `transversalCNOT`/`transversalBatch` (the incidence must INDUCE
  the requested logical CNOT — `checkTransversalCNOT(Batch)` rejects the zero map). **GPPM
  is NOT a verified compile rule** (the fake `gppmRealization` that re-emitted native `.ppm`
  + obligations was removed — without a capability it failed exactly like native PPM):
  `measure` compiles by native PPM or WITNESSED-capability PPM only, and the `QLDPCPapers` chain-cert
  protocols are a SEPARATE, explicitly-UNVERIFIED `ExternalClaim` layer (Γ-bound +
  non-degenerate / rank-checked, zero-map-rejecting; induced action is `externalProtocolCert`).
  The external GPPM target is GENERALIZED (`gppmTargetWf`: nonempty, no-dup, on-data-block,
  valid) and so ACCEPTS high-weight (>2-body) Paulis the native `MTarget.wf` rejects — but it
  is still only an `ExternalClaimArtifact`, never a `CheckedPrimitive`/`WellTyped`.
  **CHAIN↔SYMPLECTIC BRIDGE (verified, transversal-realizable subclass):** `homCNOTBridge?`
  FIRST requires the full protocol binding — `homCNOTBoundOk Γ p` (direction/dims/transversality/
  NON-DEGENERATE rank/frame, blocks live+distinct), the recorded chain-commutation/stabilizer
  flags, and a NONTRIVIAL requested logical incidence (a no-op/zero map is rejected) — THEN feeds
  the chain cert's width-`n` `PhysMap` as a physical incidence to the VERIFIED
  `checkTransversalCNOTBatch`, which LIFTS it to the width-`2n` symplectic `cnotMap` and checks the
  INDUCED logical action mod the actual `Γ` stabilizer; `homCNOTBridge_sound` PROVES the induced
  logical CNOT and `homCNOTBridge_bound` PROVES the protocol was bound (axioms
  `propext, Classical.choice, Quot.sound`, inherited from `checkTransversalCNOTBatch_sound`).
  This is the FIRST induced-action (not just legality) theorem at the chain-cert boundary; the
  VERIFIED content is structural protocol binding + induced transversal logical CNOT action.
  STILL DEFERRED: the chain-level homology commutation `∂φ=φ∂` is a RECORDED CLAIM (required set,
  not recomputed — no boundary maps are carried), and a full GPPM (ancilla prep + measurement-
  outcome + frame) stays deferred, so GPPM is NOT a `CheckedPrimitive` (`gppmBridgeHomCNOT?`
  requires `gppmBoundOk` then bridges the hom-CNOT only).  A non-transversal `PhysMap` is rejected
  at BOTH layers (`homCNOTBoundOk` itself requires `physicallyTransversal`); what stays a pure
  `ExternalClaim` is a TRANSVERSAL cert whose induced action is not bridged.  See the ChainQ2Mixed
  README "Paper-readiness matrix" for the full tiering with Lean entry points.
  SCOPE: logical-legality + addressing + resource (SSA / ancilla address+basis /
  use-after-discard) soundness only; ancilla *state preparation*, QStab lowering, syndrome
  extraction, decoder, FT, operational equivalence remain DEFERRED obligations, never
  silently assumed.
- `Source → Mixed` = `compile?` — sound (`compileProgramLocA_sound`). **The contract.**
- `Mixed → exec` = `execMixed` — `.pauli`/`.transversal` aligned (`step_pauli_matches_exec`); `none`/stuck on gadget/switch/magic.
- `PPM-measurement → QStab` = `ppmMeasToQStab` — **skeleton, no soundness theorem** (one measurement).
- `CodeSwitch` certificates — **external/assumed** (`structuralCheck` = shape/direction/claim only).

**NOT implemented (DESIGN.md plan only — do not cite as existing):** `ChainQ→PPR`
(`elabChainQ_denote`), `PPR→PPM` (`lowerProg_denote`), `PPM→LS`/full LS IR,
`LS→QStab` (`ls_to_qstab_sound`) and the physical-channel part of `QStab→QClifford`,
plus the
**magic (T) discharge** (MagicQ). These are multi-milestone and named here so the
contract cannot be mistaken for end-to-end.

## §3. Gadget-correctness boundary (`Compiler.GadgetBoundary`, `opBoundary`)

Every lowered op is tagged with the level at which its correctness is established
(`Compiler/Mixed/Semantics.lean`; facts in `Demo/Contract.lean §5`):

| Boundary | Meaning | Ops | Witness |
|---|---|---|---|
| **`exact`** | emitted `Step` matches the ideal simulator (`execMixed`) | direct `hGate`/`sGate` (k=1), `xGate`/`zGate`, `blockTransversal` H/S | `step_pauli_matches_exec`, `Step_transversal_realizes`, Demo §5 (D) |
| **`idealChannel`** | type-checks + `Step` evolves classical store + Pauli frame; carrier channel (`QInterp.proj`) UNCONSTRAINED = ASSUMED ideal | `cnotGate`/`czGate`, multi-logical `hGate`/`sGate`, `measure` | frame-progress `progCNOTAt_steps`/`progCZAt_steps`/`progSAt_steps`/`progHAt_steps` (P, frame-level only) |
| **`typecheckedOnly`** | lowers + type-checks (`compileOp_sound`); NO `Step` | `tGate` (deferred magic) | `compileOp_sound` (P) |
| **`provenChannel`** | physical carrier channel proven correct | — none yet — | (future) |

`czGate` additionally rides the **experimental placeholder** `progCZAt` (its measurement
pattern is shaped to type-check; the exact CZ channel is not modeled). M22 proved its
*frame-level* progress (`progCZAt_steps`), removing the asymmetry vs. H, but the carrier
channel stays `idealChannel`/assumed.

## §4. `SupportedSourceProgram` (the demo compiler's fragment contract)

`SupportedSourceProgram mode cfg Γ ops := sourceCompilable mode cfg Γ ops = true`
(`Mixed/Lower/Public.lean`). It MEANS: operands well-formed; **every op lowers** (a
well-formed-but-unimplementable op makes `compileProgramLocA` `.error`, never a silent
placeholder); required `caps` present; mode magic policy holds. **Resources are
IDEAL-ASSUMED** (fresh ancillas from the address seed `cfg.anc`, not a threaded
`ResourcePool`). It is DISTINCT from operational exactness (`exactSupportedOp`): a
supported program may include ideal-channel gadget lowerings.

Proved/tested: `SupportedSourceProgram.wellFormed` (a, P), `SupportedSourceProgram.checks`
(b, P — output passes `checkLogicalExecAux`), `Demo/Contract.lean §4` (c, D), the exact
fragment vs. simulator in `Demo/Frames.lean §5` (d, D).

### The three end-to-end contract examples (`Demo/Contract.lean`)
1. **Exact direct** — `H;S` run through `execMixed` equals the ideal source run (D).
2. **PPM gadget, ideal-channel** — Bell-prep CNOT compiles + type-checks with an adapter
   cap; `execMixed` is `none`/stuck on the gadget (channel NOT run) (D).
3. **Library-inspired code switch** — `MixedInstr.switch 0 repCode3 {kind:=.gaugeFix, f:=encF}`
   type-checks with the **proved symplectic** `checkSwitch` cert (D); a bad-shape cert is
   rejected.

## §5. Library coverage (Task 4)

**P/D/A/M** classifications and minimal-next per paper family (grounded in
`Library/verified_compilation_pipeline_notes.md`; no PDFs fetched).

| # | Paper family | Required syntax / op / cert | LogicQ has | Missing feature / proof | Minimal next |
|---|---|---|---|---|---|
| 1 | **HGP / homological product** (0903.0566, 2407.18490, 2411.03646) | product CSS constructor; chain maps; parallel PPM via homomorphic CNOT | `ChainQ.Internal.hgp`/`hgp?`, `symplecticStabilizers`; `chainComplex_css` (only ∀-thm) | chain-MAP object between codes; per-instance `cssCondition` (D) not ∀ | `∀` `hgp_cssCondition` via `chainComplex_css`; `ChainQ.CodeMap` (∂f=f∂ over GF2) |
| 2 | **BB / lifted / balanced / bootstrap product** (2012.04068, 2410.03628, 2012.09271, 2601.22363) | ring-backed (F2[G]) product constructors | `ChainQ.Internal.bb`/`liftedProduct` (univariate circulant) | balanced/bootstrap product; general F2[G] | add `BalancedProduct`; fix BB grounding citation |
| 3 | **qLDPC surgery / adapters** (2407.18393, 2410.03628, 2410.02213, 2503.05003) | Merge/Split/Bridge/Adapter IR + metrics; merged-CSS cert | `Capability` (5 `CapKind`s) + `checkPPM`/`checkPPM_merged_sound` (P); `SurgeryCert` (record) | Surgery/Adapter IR nodes + metric fields; `claimed*` not decided | lift `claimedMergedCommutes` to `sympOrthogonal` check; add metric fields |
| 4 | **Code switching / dimension jump** (2510.07269, 2409.13465, 2510.08552) | typed protocol step + induced-map/injectivity cert; success/failure branch | `TypeChecker.SwitchCert`+`checkSwitch_sound` (P, symplectic); `CodeSwitch.SwitchProtocolCert` (A, external) | success/failure protocol branching; switch as source op | promote `claimedChainCommutes`/`claimedInjective` to GF(2) checks |
| 5 | **Batched high-rate ops** (2510.06159) | batch axis; `batchedSwitch` capability; batched syndrome | — only a `disjointFromOthers` Bool placeholder | **batch axis entirely absent** (LogicQ's named differentiator) | `structure Batch` + `checkBatchedOp` (fold gadget over blocks) + `CapKind.batchedSwitch` |
| 6 | **PPR/PPM scheduling** (2605.23738, 2503.05003) | PPM Layer/group + pairwise-commutation; equivalent-generator rewrite | `ChainQ2Mixed.Schedule`: `Layer`/`Schedule`/`ScheduleMode`, the **stratified** cert `mtargetDisjoint`⊂`mtargetSameOrId` (ancilla-free) ⊂`mtargetCommute` (ancilla-required), `compileScheduled?`→proof-carrying `CompiledSchedule` (P); outcome-var SSA (`checkPPMStmt` `outcomeReused`) (P) | `Schedule → QStab` lowering (only `scheduleCoords`→`QStab.Sched` computed); `commutingWithAncilla` twist-free/ancilla realization; `Schedule→Schedule` rewrite rules | carry `scheduleCoords` into `QStab.Sched` on each `prop`; discharge the ancilla obligation; add `equivGenerators` rewrite (span-eq both ways) |
| 7 | **Magic-state inject/distill/cultivate** (2505.06981, …) | MagicQ protocol; RepeatUntilSuccess; resource states | — only a typed `MagicObligation` with NO `Step` (A, the T-hole) | factory verification; success/failure semantics | MagicQ AST (`RepeatUntil` + `Success` predicate); keep factory circuits as named obligations |
| 8 | **QStab/QClifford detectors** (quant-ph/0406196, 2103.02202, 2501.14380) | detector parity defs; DEM; tableau equivalence | `QStab.eval`/`evalVar` (classical, `eval_length` P); `detectorsDeterministic?` (D); `QClifford.run` | quantum back-action (deferred `proj` hook); no Stim/DEM; no `QStab≡QClifford` | concrete stabilizer-tableau `Host`; then `QStab.eval = QClifford` detector-parity lemma |

## §6. Deferred — with a precise plan (do not silently skip)

- **Resource/ancilla pool threading (Task 3·2) — LEGACY `Source → Mixed` path only.**
  NOTE: the named **`ChainQ2Mixed` compiler ALREADY threads a checked `AncillaPool`** (every
  gadget `AncillaPool.alloc`s a valid/live/right-basis/available ancilla, consumed once; the
  outcome is in `CompiledMixIR.poolOut`). What remains deferred is the OTHER, legacy entry
  point: `compileProgramLocA` / `compile?` still use the unchecked `AncillaSupply` address
  counter. Thread `AncillaPool` there too: replace `sup.alloc.1` with
  `AncillaPool.alloc Γ R basis pool` (adds an `.error` arm; `compileProgramLocA_sound`'s
  conclusion is unchanged — same `compileOp_sound` + IH, plus the trivial error case). HIGH
  churn: changes the public `compile?`/`CompileConfig` signature and every Demo `decide` that
  fixes `anc := ⟨b,i⟩`. The correctness GAIN (every gadget ancilla `validLQubit ∧ ¬dead`) is
  real; deferred until lower-churn items settle. (Both paths leave ancilla STATE preparation a
  declared `logicalAncillaDeferred` obligation — the basis is a tag, not an operational proof.)
- **`provenChannel` for any gadget.** Requires constraining `QInterp.proj` to the physical
  projector and proving the gadget channel = ideal unitary up to frame (genuine new math).
  `GadgetBoundary.provenChannel` exists precisely to name this unfilled tier.
- **Full progSAt/progCNOTAt frame TABLES** (per-outcome byproduct, like `progHAt_frame`):
  the M22 work proved *existence-of-skip* progress; the full 4-/8-branch tables are deferred.
- **Proposed language extensions** (Task 5, prioritized in §5): batch axis (#5), PPM
  layer+scheduler (#6), GF(2)-decided `ChainMapCert`/`CodeMap` (#1/#4), MagicQ AST (#7).
  M22 implemented the smallest concrete steps — the `GadgetBoundary` correctness-boundary
  record and the proved-cert `switchRepInstr` example — and names the rest as obligations.
