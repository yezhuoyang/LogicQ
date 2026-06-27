# LogicQ compiler contract (M22)

**Read this first.** The implemented compiler targets the **Mixed IR**
(`Compiler.MixedInstr`). The linear pipeline `ChainQ → PPR → PPM → LS → QStab →
QClifford` in `DESIGN.md` is the **intended/future** plan: `PPR`, `QStab`, `QClifford`
are *verified standalone language specs* (syntax + semantics + laws, axiom-clean) that
**no compiler pass yet wires together** — `Compiler/{ChainQ2PPR, PPM2LS,
QStab2QClifford}` are empty stubs. The **only end-to-end wired path** is
`Source LogicalOp → Mixed IR` (via `compile?`), plus a one-measurement skeleton bridge
`Mixed/PPM → QStab` (`ppmMeasToQStab`) and the external/assumed `CodeSwitch` certificates.

No `sorry`/`admit`/`native_decide` anywhere in `Compiler`; soundness theorems are
axiom-clean (`propext`/`Quot.sound` only).

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
| **4 Mixed IR** (target) | `Mixed/Syntax.lean` `MixedInstr` (`ppm`/`transversal`/`automorphism`/`switch`/`magic`/`pauli`) **P** | `Mixed/Check.lean` `checkInstr`/`checkLogicalExec` (threads `TypedEnv`+`PPMState`) **P** | operational `Step`/`Steps` (parametric `MixedInterp`) **P** | `compileOpR` (from Source) | `execMixed` (exec); `ppmMeasToQStab`/`CodeSwitch` (bridges) | `compileProgramLocA_sound`, `compileOp_sound`; `Step_implies_checkInstr`, `no_step_magic`, `Step_transversal_realizes`, `Step_pauli_realizes`, `step_pauli_matches_exec` **P** | `compileOp_complete_{measure,hGate,sGate}`, `ProgramOkSupported_compiles` (supported fragment) **P** | Demo §1/§5/§5b/§7/§8/Contract **D** | **resource pool not threaded** through `compile?` (`AncillaPool.alloc_valid` proven but unused) **M/A**; `magic` has no `Step`; execMixed multi-block transversal is per-qubit realization, not literal `Step` equality |
| **5 Surgery/Adapter** (`LS2QStab`+`CodeSwitch`) | no distinct LS IR (`LatticeSurgery/` empty) **M**; `SurgeryCert`, `CodeSwitch.SwitchProtocolCert`, Mixed `MixedInstr.switch`+`SwitchCert` **P** | `SurgeryCert.check`/`detectorsDeterministic?`, `*.structuralCheck` (shape/claim only); symplectic `checkSwitch` (GF(2)-decided) **P** | none operational (skeleton) **A** | `ppmMeasToQStab` (one meas) | into QStab `Prog` | `checkSwitch_sound`, `checkPPM_merged_sound` **P**; LS2QStab pass-soundness **M** | none **M** | `progZZ`/`certZZ`, `goodSwitch`, `switchRepInstr` (Contract §3) **D** | distance/fault-distance/decoder **A** (all `FaultStatus.deferred`); `claimed*` recorded, not decided; `CodeSwitch` certs EXTERNAL/ASSUMED |
| **6 QStab** | `QStab/Syntax.lean` `Stmt`(prop/parity)/`Prog` **P** | only `Prog.wf` (Bool, SSA) **M** | classical dataflow `eval`/`evalVar` (`eval_length` **P**) | `ppmMeasToQStab` | none (`QStab→QClifford` planned) **M** | none (pass) **M** | none **M** | `progReadout` evals **D** | quantum back-action = deferred `proj` hook **A**; no Stim/DEM export **M** |
| **7 QClifford** | `QClifford/Syntax.lean` `Gate`/`Circuit` **P** | none (resource readouts only) **M** | operational `run` over parametric `Host` (`run_append` **P**) | none (from QStab) **M** | — (terminal) | `run_append` (composition) **P**; pass-soundness **M** | none **M** | `cnotFromCZ` **D** | concrete `Host` (tableau) **A**; real sim is `Compiler/Simulator` on Mixed |

## §2. Wired edges vs. not-yet-wired passes

**Wired (real) edges:**
- `Source → Mixed` = `compile?` — sound (`compileProgramLocA_sound`). **The contract.**
- `Mixed → exec` = `execMixed` — `.pauli`/`.transversal` aligned (`step_pauli_matches_exec`); `none`/stuck on gadget/switch/magic.
- `PPM-measurement → QStab` = `ppmMeasToQStab` — **skeleton, no soundness theorem** (one measurement).
- `CodeSwitch` certificates — **external/assumed** (`structuralCheck` = shape/direction/claim only).

**NOT implemented (DESIGN.md plan only — do not cite as existing):** `ChainQ→PPR`
(`elabChainQ_denote`), `PPR→PPM` (`lowerProg_denote`), `PPM→LS`/full LS IR,
`LS→QStab`/`QStab→QClifford` (`ls_to_qstab_sound`, `qstab_prop_extracts`), and the
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
| 6 | **PPR/PPM scheduling** (2605.23738) | PPM Layer/group + pairwise-commutation; equivalent-generator rewrite | — `PPR2PPM` is fragment evidence, not a scheduler | commuting-measurement grouping + verified rewrite | `PPM.Layer` + `pairwiseCommute` (sympForm) + `equivGenerators` rewrite (span-eq both ways) |
| 7 | **Magic-state inject/distill/cultivate** (2505.06981, …) | MagicQ protocol; RepeatUntilSuccess; resource states | — only a typed `MagicObligation` with NO `Step` (A, the T-hole) | factory verification; success/failure semantics | MagicQ AST (`RepeatUntil` + `Success` predicate); keep factory circuits as named obligations |
| 8 | **QStab/QClifford detectors** (quant-ph/0406196, 2103.02202, 2501.14380) | detector parity defs; DEM; tableau equivalence | `QStab.eval`/`evalVar` (classical, `eval_length` P); `detectorsDeterministic?` (D); `QClifford.run` | quantum back-action (deferred `proj` hook); no Stim/DEM; no `QStab≡QClifford` | concrete stabilizer-tableau `Host`; then `QStab.eval = QClifford` detector-parity lemma |

## §6. Deferred — with a precise plan (do not silently skip)

- **Resource/ancilla pool threading (Task 3·2).** Thread `AncillaPool` (already proven
  `alloc_valid`) through `compileProgramLocA` instead of the unchecked `AncillaSupply`
  address counter: replace `sup.alloc.1` with `AncillaPool.alloc Γ R basis pool` (adds an
  `.error` arm; `compileProgramLocA_sound`'s conclusion is unchanged — same `compileOp_sound`
  + IH, plus the trivial error case). HIGH churn: changes the public `compile?`/`CompileConfig`
  signature and every Demo `decide` that fixes `anc := ⟨b,i⟩`. The correctness GAIN (every
  gadget ancilla `validLQubit ∧ ¬dead`) is real; deferred until lower-churn items settle.
- **`provenChannel` for any gadget.** Requires constraining `QInterp.proj` to the physical
  projector and proving the gadget channel = ideal unitary up to frame (genuine new math).
  `GadgetBoundary.provenChannel` exists precisely to name this unfilled tier.
- **Full progSAt/progCNOTAt frame TABLES** (per-outcome byproduct, like `progHAt_frame`):
  the M22 work proved *existence-of-skip* progress; the full 4-/8-branch tables are deferred.
- **Proposed language extensions** (Task 5, prioritized in §5): batch axis (#5), PPM
  layer+scheduler (#6), GF(2)-decided `ChainMapCert`/`CodeMap` (#1/#4), MagicQ AST (#7).
  M22 implemented the smallest concrete steps — the `GadgetBoundary` correctness-boundary
  record and the proved-cert `switchRepInstr` example — and names the rest as obligations.
