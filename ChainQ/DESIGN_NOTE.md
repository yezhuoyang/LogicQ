# ChainQ hardening — design note

Strengthening pass making ChainQ a solid, general foundation for real qLDPC code
families before any compiler work. Everything is Mathlib-free and checkable by
`decide`. Builds verified: `lake build ChainQ`, `lake build TypeChecker`,
`lake build LogicQ` all succeed.

## M5 addendum (trustworthy core + TypeChecker integration)

The second pass (M5) closed the two biggest gaps the first pass had deferred and
hardened the constructors:

- **Circulant ring canonicalized** ([Ring.lean](Ring.lean)): a single
  `circNorm ℓ` (exponents mod ℓ of ODD multiplicity, GF(2) cancellation) is now
  the source of truth; `circulant`, `circDagger`, `circMul`, `biCirculant`, and
  the lifted product all route through it. Regression: `circulant 3 [0,0] =
  zeroMat 3 3` (NOT identity), `circulant 3 [3] = identMat 3`.
- **GF(2) kernel-basis finder + derived logicals** ([Kernel.lean](Kernel.lean),
  [Params.lean](Params.lean)): `kernelBasis`/`kernelBasis?` (RREF
  back-substitution right-kernel), `quotientBasis` (independent mod a row span),
  `gf2Inv` (augmented-RREF inverse). `deriveLogicalBasis? : CSSCode → Option
  CSSLogicalBasis` computes X̄ from `ker Hz / rowSpan Hx`, Z̄ from `ker Hx /
  rowSpan Hz`, dualizes via `gf2Inv` so `gemmT lx lz = I_k`, and returns `some`
  ONLY when `c.valid` and the produced basis re-passes `CSSLogicalBasis.valid`.
  Tested: derivation succeeds for `bareQubit`, `xCheck2`, `surface 2`, `toric 2`.
- **Shape-safe checked constructors** ([Families.lean](Families.lean)): `hgp?`,
  `surface?`, `toric?`, `bb?`, `liftedProduct?` reject declared-vs-actual shape
  disagreement and degenerate parameters (`d < 2`, `ℓ = 0`, `rA ≠ A.length`).
- **`CSSLogicalBasis.valid` now guards on `c.valid`** — a malformed/ragged code
  is rejected even if a supplied basis is shape-correct.
- **TypeChecker row safety patched** (no longer deferred):
  `PPM.factorRep → factorRep?` (via `row?`); `checkPPM` rejects out-of-range
  logical indices with `TypeError.badLogicalIndex` instead of treating them as
  identity; `Switch.rowsEqualModSpan` is row-count + width checked; `checkSwitch`
  checks both X̄ and Z̄ arity. Negative tests added for both.

The "what was implemented" sections below describe the first pass; the M5
changes above supersede the matching "NOT implemented" bullets.

## M10 addendum (PL-solid mixed IR)

**Design shift, stated plainly: PPM is ONE checked target sublanguage; the Mixed
IR is the compiler target; correctness is expressed through ONE semantic relation
(`Compiler.Step`/`Steps`) shared by all coexisting IR fragments.**

- **Resource soundness** ([Compiler/Mixed.lean](../Compiler/Mixed.lean)): `checkInstr`'s
  transversal / automorphism / switch cases now consult the threaded resource
  state — a direct operation on a block holding ANY discarded logical qubit is
  rejected (`discard q ; transversal/automorphism/switch b` all reject).
- **Normalized `DeadSet`** ([PPMProgram.lean](../TypeChecker/Judgment/PPMProgram.lean)):
  the discard set is a dedup'd finite set with `insert`/`union`/`subset`; branch
  joins use `union` (not list append) and the loop "discards nothing" test uses
  `subset` (not length).  `checkPPMStmt_dead_mono` / `…_no_use_after_discard`
  re-proved over the set ops.
- **PL judgments** ([Compiler/MixedSemantics.lean](../Compiler/MixedSemantics.lean)):
  source typing `srcOpOk` (`Γ; R ⊢ op ok`); the resource-aware compilation
  relation `compileOpR` (`Γ; R ⊢ op ⇝ instr ⊣ Γ'; R'`) lowering through the
  checker.  **`compileOp_sound`** (the emitted instruction type-checks) and
  **`compileOp_complete`** for the supported fragment (a checkable measurement, a
  legal transversal H lower successfully).
- **`compileProgram`** threads `TypedEnv`, the resource state, and fresh classical
  vars; **`compileProgram_sound`** — a compiled program is accepted by
  `checkLogicalExecAux` (well-typed by construction).
- **One shared operational semantics**: `ExecState {env, resource, frame,
  classical, quantum}` with a parametric quantum carrier; `Step`/`Steps` over
  `MixedInstr`.  **Per-instruction realization** (`Step_transversal_realizes`,
  `Step_automorphism_realizes`: the direct fragment transforms the carrier by
  exactly its symplectic Clifford action) and **sequential composition**
  (`Steps_append`).  `transversal_step_matches_action` ties the step to
  `MixedInstr.action`.  All ∀-theorems are sorry-free (`propext`(/`Quot.sound`)).
- **Honest deferrals**: full PPM-gadget unitary/channel semantics (so realization
  is exact for the DIRECT fragment, frame-level for PPM); `compileOp_complete` for
  the gadget-fallback and CNOT paths; richer ancilla allocation / obligation
  collection; and the **simulator + Deutsch–Jozsa/Grover/Simon** examples
  (Stage 7) — deferred this pass by chosen priority (PL-theory depth).

Post-review (adversarial pass, 4 fixed): (a) **`srcOpOk` is now load-bearing** —
its resource component is aligned to the checker's semantics (block-level for
direct ops, qubit-level for measure) and **`srcOpOk_hGate_compiles`** proves
`Γ;R ⊢ H q ok` + a legal transversal ⇒ `H q` compiles to a direct transversal
(source typing drives compilation, not decorative). (b) The shared `Step` now also
has a **`switch`** rule (env transforms, quantum preserved — `Step_switch_preserves_quantum`),
so it covers the transversal/automorphism/switch fragments; the docstring honestly
scopes that `ppm`/`magic` dynamics are deferred. (c) Discriminating `decide` tests
added for the `DeadSet` ite-union join and the loop-`subset` rejection.

## M11 addendum (close the compiler contract + exact simulator)

Goal: close the source→Mixed-IR contract before lower-stack work, and validate it
with an exact simulator.

- **Source PROGRAM typing** (`Compiler.MixedSemantics`): `ProgramOk Γ caps res ops`
  threads `Γ`, the PPM resource state, and a fresh-CVar counter, and checks ALL the
  source conditions per op: valid/live/not-discarded operands (`srcOpOk`), PPM
  legality + capability availability (`checkPPMProgram` under `caps`), CNOT
  `control ≠ target`, the T/MAGIC POLICY (`Resources.allowMagic` — `false` until
  `MagicQ`), the FRESH-CVAR discipline (a measurement's outcome var is the threaded
  fresh slot and unbound), and ANCILLA availability (`validLQubit Γ res.anc`).
- **Supported-fragment completeness**: `ProgramOkSupported_compiles` — the direct
  transversal-legal `H`/`S` fragment (Γ/R invariant) always COMPILES
  (`compileProgram` succeeds), proved by composing the per-op progress lemmas
  `srcOpOk_{h,s}Gate_compiles`. Axiom-clean (`propext`).
- **Logical LOCATION / alias map** (`LocMap`): a PPM `H`/`S` gadget TELEPORTS the
  logical state to an ancilla; `relocateOnFallback` relocates the CANONICAL name
  `q ↦ anc` exactly when the emitted instruction is a `.ppm` gadget (a direct
  transversal does not teleport), and `compileProgramLoc` RESOLVES each op's
  operands through the map (`LogicalOp.resolve`) before lowering.
- **Exact ideal simulator** (`Compiler.Simulator`): a Mathlib-free Gaussian-integer
  (`GInt`) state-vector simulator (`H`/`S`/`X`/`Z`/`CNOT`/`CZ`, unnormalised — a
  fixed `H`-count shares one global `1/√2^k` scale, so unnormalised comparison is
  faithful). Runs **Deutsch–Jozsa** (constant ⇒ query 0, balanced ⇒ query 1),
  **2-qubit Grover** (finds `|11⟩` with certainty), and **Simon n=2** (`s=11` ⇒
  measured input uniform over `{00,11}`), all validated `by decide`. Source-vs-
  lowered: `compileToGates` lowers a program through the real `compileOpR` and, on
  success, records the realised gate sequence; for the direct `H;S;H` fragment the
  source and lowered state vectors are decided EQUAL.
- **Deprecation**: the M9 resource-LIGHT selector (`cost`/`firstLegal`/`compileOp`
  + its legacy theorems) is now `private` — superseded by the resource-aware
  `compileOpR`/`compileProgram`, onto which the direct-fragment SEMANTIC
  correctness migrated as `compileOpR_{h,s}Gate_action_sound`.
- **Honest deferrals (per chosen priority)**: evidence-carrying `MixedInstr`/`Step`
  and PPM.Semantics `Step` integration (Stage 4) deferred; full PPM-gadget channel
  semantics still deferred, so the CNOT/measurement gadgets lower through the
  type-checker and realise their logical op under the ideal-gadget ASSUMPTION (the
  simulator's source=lowered equality is decided exactly only for the direct
  fragment).

Post-review (adversarial pass, 4 fixed — 1 medium, 3 low, 0 soundness holes; 21
confirmed-ok, 3 false alarms): (a) **ancilla condition made coherent** — `progOpOk`
now applies `validLQubit Γ res.anc` UNIFORMLY (added to `tGate`, which a magic
injection needs), documented as a CONSERVATIVE precondition (H/S may fall back to a
teleport gadget, CNOT always does, T needs a magic ancilla) rather than a
per-path resource count. (b) The simulator's source-vs-lowered docstrings were
**rewritten to drop the overclaim**: `compileToGates` records each op's IDEAL gate
(`opGate?`) and DISCARDS the emitted instruction's channel, so the equality
certifies *the program lowers* + (under the ideal-gadget assumption, exact at the
symplectic level for the direct fragment via `compileOpR_*_action_sound`)
distribution agreement — it is not an independent gadget-channel re-simulation. (c)
The redundant-but-defensive `! R.bound.contains r` fresh conjunct is documented as
belt-and-suspenders. `ProgramOk`/`progOpOk` remain test-only (not load-bearing for
any theorem), so none of this touched a verified result.

## M12 addendum (evidence-carrying Mixed/PPM semantics contract)

Goal: close the source→Mixed→(PPM-step) contract before lowering further.  **Mixed
IR is the compiler target; PPM coexists with transversal gates, automorphisms,
switches, and magic obligations; checked emitted programs step through the SAME
semantics the type-checker accepts.**  Grounded in the local sources (PPM-as-
adaptive-channel 1506.01396; surgery/detectors 2407.18393; adapters/merged-CSS
2410.03628; code-switching 2510.07269/08552; FT-verification deferrals 2501.14380).

- **M11 contract bugs fixed.** (A) **T/magic mismatch**: `compileOpR` now lowers `T`
  to a checker-ACCEPTED `.magic` *deferred obligation* (no `Step` semantics), and
  `ProgramOk` admits `T` only under `allowMagic`, and `compileProgram` then lowers
  it — so a `ProgramOk`-accepted `T` is no longer uncompilable (the M12 mismatch is
  closed for `T`).  This is NOT a global completeness claim: other well-typed ops
  (e.g. a `CNOT` with no available gadget/adapter) still fail compilation with an
  explicit error — completeness is proven only for the supported fragment
  (`ProgramOkSupported_compiles`).  (B) **LocMap repeated
  teleport**: `compileProgramLoc` relocates the CANONICAL name (the original op),
  not the resolved one, so `q0 ↦ q1 ↦ q2` resolves to `q2` (regression test).  (C)
  **Simulator layout**: an explicit `Layout : LQubit → Nat` respects BOTH block and
  logical index (same-block `⟨0,0⟩`/`⟨0,1⟩` map to distinct sim qubits).
- **Evidence-carrying operational semantics** (`MixedSemantics` §4).  `Step I caps`
  rules each have a `checkInstr … = .ok (Γ', R')` premise and step to that CHECKED
  `(Γ', R')` — no rule runs a raw instruction with an invented env.  Theorems
  (axiom-clean, `propext`): `Step_implies_checkInstr` (step ⇒ acceptance),
  `no_step_of_checkInstr_error` / `no_step_of_not_accepted` (rejected instruction
  cannot step), **`Step_switch_uses_checked_env`** (switch uses the `checkSwitch`
  target env), `Step_switch_preserves_quantum`, the direct realization theorems
  (preserved from M10), `progress_*` + `progress_ppm_progH` (no-stuck for the direct
  + PPM subset), and `Steps_append`.
- **PPM-Step integration** (task 4).  `MixedInterp` now carries a `PPM.QInterp`; the
  `Step.ppm` rule DELEGATES the quantum/classical/frame channel to a terminating
  `PPM.Steps` run (`ppm_step_lifts_ppm_semantics`).  Outcomes + Pauli frame are
  threaded by `PPM.Semantics` (`Store`/`Frame`).  This claims interface-level
  evolution, NOT end-to-end gadget unitary correctness.
- **Public proof-carrying path** (tasks 2–3).  `CompiledMixed {prog, …, typed}`
  carries `checkLogicalExecAux … = .ok …`; `compileMixed?` is the public entry and
  is sound by **`compileProgramLoc_sound`** (the emitted program type-checks, hence
  — via the dead-guards — uses no discarded resource).  Completeness: the direct
  transversal `H`/`S` fragment compiles (`ProgramOkSupported_compiles`, M11);
  unsupported gates fail with explicit errors.
- **QStab bridge SKELETON** (task 5, `LogicalToQStab`).  One logical PPM measurement
  → a QStab `prop`+`parity`; a `SurgeryCert` records measured parity, preserved
  logicals, byproduct/frame, merged-CSS commutation, detector determinism, with
  **deferred obligations** (distance / fault-distance / decoder) explicit and
  uncertified.  Detector determinism is checked via `QStab.eval`.
- **Simulator harness** (task 6).  Decodes the EMITTED transversals (`loweredGates`)
  and compares the emitted program's distribution to the source — exact for the
  direct fragment; PPM gadgets stay the labeled ideal-gadget assumption.  A
  measurement-with-classical-outcome example runs through `PPM.Steps`.
- **Deferred (honest)**: full PPM-gadget channel unitary correctness; full
  lattice-surgery construction (distance/fault-distance/decoder); full magic
  semantics.  Magic type-checks but does not execute.

## M13 addendum (close remaining PL contract gaps in Mixed IR)

Goal: close the PL gaps M12's review surfaced before deeper QStab/QClifford lowering.

- **Magic / executable split** (M13 task 1 + 5; fixes M12 `magic-hole` + the T
  overclaim). The compiler now has TWO public entries: `compileMixed?` (EXECUTABLE
  — returns `ExecutableMixed`, requiring `progNoMagic`; REJECTS `T`/`.magic`) and
  `compileMixedModuloMagic?` (TYPED modulo magic — may carry `.magic` obligations).
  `MixedInstr.isMagic`/`progNoMagic` separate the two; `no_step_magic` proves a
  `.magic` instruction cannot step (typed, never executable).  The M12 doc overclaim
  ("no well-typed-but-uncompilable program") is corrected — completeness is proven
  only for the supported fragment; e.g. a `CNOT` without an adapter still fails.
- **Block-level direct gates** (task 2). NEW `LogicalOp.blockTransversal b g` is the
  HONEST block-level direct transversal (acts on the whole block, `srcAction` =
  block-wide `transversalMap`); `compileOpR` emits `.transversal b g` for it.
  `hGate q`/`sGate q` are documented as SINGLE-LOGICAL-BLOCK shorthand (honest when
  the block has one logical qubit, e.g. `tenvQ`, where they coincide with the block
  op — proven by `srcAction` equality).  Full per-logical enforcement on
  multi-logical blocks (an induced-logical-action certificate / a `k=1` compile
  guard) is a documented DEFERRAL — see "remaining PL design risks".
- **Ancilla allocation** (task 4; fixes M12 `single-anc-reuse`). NEW `AncillaSupply`
  + `compileProgramLocA` (sound: `compileProgramLocA_sound`, propext) allocate a
  FRESH ancilla per op, so repeated PPM fallbacks never reuse one; the public path
  routes through it.  Tests: successive `alloc`s are distinct; two fallbacks on the
  same canonical qubit relocate it to the NEWEST (distinct) ancilla.
- **PPM gadget progress** (task 3). NEW `progHAt_steps` + `progress_ppm_progHAt`
  prove FRAME-LEVEL progress (a terminating `PPM.Steps` run ⇒ a Mixed `Step`) for
  the PARAMETERIZED emitted H gadget `progHAt q anc r₁ r₂` (M12 only covered the
  fixed `progH`).  `progSAt`/`progCNOTAt` Step-level progress is DEFERRED (nested-
  conditional gadgets); they still type-check.  No full gadget unitary/channel
  correctness is claimed.
- **QStab certificate honesty** (task 7). `SurgeryCert`'s asserted Bools renamed
  `claimed…`; NEW `SurgeryCert.check` verifies the COMPUTABLE invariants (parity
  non-empty, a preserved logical, ALL deferred obligations `false`), and detector
  determinism is checked via `QStab.evalVar`.  Distance / fault-distance / decoder
  remain explicitly `false`/deferred.
- **Simulator honesty** (task 6). DJ/Grover/Simon are labeled SOURCE-circuit
  validation (not lowered-program correctness); the source-vs-EMITTED equality is
  decided only for the direct fragment (`mixedInstrToGate?` returns `none` for PPM
  gadgets, so a fallback program is excluded from equality tests, not silently
  mismatched).

REMAINING PL DESIGN RISKS (honest): (1) `hGate`/`sGate` on a MULTI-logical block are
not yet rejected/enforced at compile time — only documented as single-logical
shorthand + the honest `blockTransversal` alternative is provided; a `k=1` compile
guard (cascading through the completeness/action theorems) is deferred.  (2)
`progSAt`/`progCNOTAt` have no operational Step-level progress yet.  (3) the
end-to-end PPM-fallback + ancilla-allocation path is exercised by unit tests but not
by a multi-logical end-to-end fixture (none in-repo; the fallback needs a code where
H is not transversal).

## M14 addendum (proof-carrying resources + addressability cleanup)

Goal: close the resource/addressability gaps M13 left, before deeper QStab/QClifford
lowering.  All grounded in the local sources (PBC/magic 1506.01396; surgery 2407.18393;
adapters 2410.03628; dimension jump 2510.07269; code-switching 2510.08552;
tableau testing quant-ph/0406196; FT-verification obligations 2501.14380).

- **Addressability (task 1; closes the M13 design risk).**  `blockTransversal b g` is
  the BLOCK-WIDE direct transversal (acts on the whole block).  `hGate q`/`sGate q`
  are SINGLE-LOGICAL ops: `compileOpR` lowers them to a direct `.transversal` ONLY
  when `singleLogicalBlock Γ q.blk` (`k = 1`, where the block transversal IS the qubit
  gate); on a multi-logical block they take the qubit-level PPM gadget or FAIL with an
  explicit error — never a block-wide transversal mislabeled as a per-qubit gate.
  `LogicalOp.srcAction` for `hGate`/`sGate` is `none` on a `k>1` block (no pretend
  block-wide action).  The cascade theorems (`compileOp_complete_*`,
  `srcOpOk_*_compiles`, `compileOpR_*_action_sound`, `ProgramOkSupported_compiles`)
  carry the `singleLogicalBlock` hypothesis; tests use a valid `k=2` fixture
  `tenvQ2`.  (axiom-clean: `propext`.)
- **Source-typed modulo-magic + typed obligation (task 2).**  `.magic` now carries a
  TYPED `MagicObligation { kind, target, requiresMagicState }` (not a bare string).
  `compileMixedModuloMagic?` takes `Resources` and CHECKS `ProgramOk` first
  (`compileMixedModuloMagic?_programOk`: success ⇒ `ProgramOk = true`), so it rejects
  `T` when `allowMagic = false` and rejects an invalid `T` operand `⟨99,99⟩` BEFORE
  emitting an obligation.  The executable `compileMixed?` still rejects any
  magic-containing output (`progNoMagic` / `no_step_magic`).
- **Checked ancilla pool (task 3).**  `AncillaPool` is proof-carrying: each entry has
  a logical qubit, a `AncBasis` (`zero`/`plus`/`magicH`/`magicT`), and an `AncStatus`
  (`available`/`consumed`/`discarded`).  `AncillaPool.alloc` succeeds only for an
  AVAILABLE entry of the requested basis that is `validLQubit` and NOT discarded, and
  marks it consumed (`alloc_valid`: a successful allocation is valid + live).  Tests:
  empty pool / invalid / discarded / wrong-basis / reused-consumed all REJECTED;
  distinct allocations.  (The unchecked `AncillaSupply` of M13 remains the address
  counter threaded by `compileProgramLocA`; replacing it with the pool end-to-end is
  the next integration step.)
- **PPM gadget progress (task 4).**  `progHAt_frame` proves the FULL FOUR-BRANCH
  frame table for the PARAMETERIZED H gadget `progHAt q anc r₁ r₂` (every outcome
  pair reaches `skip` with the expected `hByp` byproduct on the ancilla) — the
  parameterized analogue of `PPM.progH_frame`.  This is FRAME/control-flow
  correctness, NOT gadget unitary/channel correctness.  `progSAt`/`progCNOTAt`
  Step-level progress remains deferred (nested-conditional gadgets).
- **Code-switch certificate skeleton (task 5; `Compiler.CodeSwitch`).**  Typed
  certificates shaped around the dimension-jump papers: `PhysMap` (physical/chain map
  + `shapeWf`), `ChainMapCert` (chain commutation + stabilizer preservation as
  claims, shape checked), `LogicalInjectionCert` (induced logical map + injectivity =
  logical transversality), `HomomorphicCNOTCert` (ONE-WAY: `matchesDirection` rejects
  the reversal; no self-CNOT), `disjointSupports` (parallel-switch disjoint-image
  condition), and `SwitchProtocolCert` with `FaultObligations` deferred.  Tiny tests:
  bad shape / non-injective / direction-reversal / self-CNOT REJECTED; disjoint vs
  overlapping distinguished.  This is a SEPARATE typed layer above the M7 `SwitchCert`
  (wiring them is the next pass).
- **QStab fault obligations (task 6).**  `FaultStatus` (`certified`/`deferred`) makes
  each obligation's status EXPLICIT; `FaultObligations { distance, faultDistance,
  decoder }` (all `deferred`) + `allDeferred`; `SurgeryCert.check` requires
  `allDeferred` (a cert that marks distance `certified` FAILS the check); detector
  determinism still checked via `QStab.evalVar`.  No merged-code distance / adapter /
  full lattice-surgery correctness claimed.

REMAINING PL RISKS (honest): (1) the checked `AncillaPool` is not yet threaded through
`compileProgramLocA` (which still uses the unchecked `AncillaSupply` counter) — pool
discipline is proved for `alloc`, not yet for whole-program compilation.  (2)
`progSAt`/`progCNOTAt` have no operational Step-level progress.  (3) the code-switch
certs are structural skeletons (chain-commutation / stabilizer-preservation /
injectivity are recorded claims, not yet decided over GF(2)).  (4) all
fault-distance / distance / decoder obligations remain deferred across PPM, surgery,
and switch certs.

## M22 addendum (compiler contract consolidation + Library coverage audit)

Goal: consolidate the end-to-end compiler contract and audit language generality vs the
Library papers — NOT new features.  Build passes; no `sorry`/`admit`/`native_decide`; no
new overclaims.  See **`Compiler/CONTRACT.md`** for the full 7-stage matrix + Library
coverage table.

- **Task 1 — contract matrix (`Compiler/CONTRACT.md`).**  7-stage matrix (Source/PPR/PPM/
  Mixed/Surgery-LS2QStab/QStab/QClifford) × (syntax/checker/semantics/passes/soundness/
  completeness/examples/deferred), each cell tagged P (proved) / D (`by decide`) / A
  (assumption) / M (missing).  Honest framing: only `Source → Mixed` (`compile?`) is a
  wired, sound pass; PPR/QStab/QClifford are isolated verified specs; the 6 DESIGN.md
  inter-level passes are named NOT-IMPLEMENTED.
- **Task 2 — `SupportedSourceProgram`** (`Mixed/Lower/Public.lean`): `abbrev := sourceCompilable
  … = true` (operands well-formed + every op lowers + caps present + magic policy; RESOURCES
  IDEAL-ASSUMED, distinct from `exactSupportedOp`).  `SupportedSourceProgram.wellFormed` (a)
  and `.checks` (b, output passes `checkLogicalExecAux`) proved by delegation;
  `Demo/Contract.lean` discharges (c)/(d) by `decide`.
- **Task 3 — gaps.**  (3·1/3·3) NEW frame-level progress theorems `progCZAt_steps`,
  `progSAt_steps`, `progCNOTAt_steps` (+ `progress_ppm_*`), via two new PPM reductions
  `red_ite_pos_into`/`red_ite_neg_into` (general nested-`ite`, no skip constraint) — lifts
  S/CZ/CNOT to the SAME frame-level progress as `progHAt`; carrier channel still A.
  `progCZAt` kept as an EXPLICIT experimental placeholder (out of `exactSupportedOp`).
  (3·4) NEW `GadgetBoundary` (`exact`/`idealChannel`/`typecheckedOnly`/`provenChannel`) +
  `opBoundary : LogicalOp → GadgetBoundary` makes the EXACT/IDEAL/DEFERRED tiers
  Lean-checked.  (3·2) checked-`AncillaPool` threading DEFERRED-with-plan (CONTRACT §6 —
  high churn, changes public signature; `alloc_valid` proven but unthreaded).
- **Task 4 — Library coverage table** (CONTRACT §5): 8 paper families (HGP, BB/LP, qLDPC
  surgery, code switching, batched high-rate, PPR/PPM scheduling, magic-state, detectors)
  with current support + missing feature + minimal-next.  Biggest gaps: batch axis (#5) and
  PPR/PPM scheduler (#6) entirely absent; magic is a pure typed-obligation hole.  Fixed the
  imprecise BB grounding citation (`ChainQ/BBCode/Basic.lean`: Bravyi 2024 not in Library).
- **Task 5 — smallest additions.**  Implemented: the `GadgetBoundary` boundary record and a
  PROVED-cert code-switch example `switchRepInstr` (`MixedInstr.switch 0 repCode3 {…,encF}`
  type-checks with the symplectic `checkSwitch`).  PROPOSED (CONTRACT §5/§6): batch axis,
  PPM Layer + commuting-measurement scheduler, GF(2)-decided `ChainMapCert`/`CodeMap`,
  MagicQ AST — named as obligations, not built.
- **Three end-to-end examples** (`Demo/Contract.lean`): (1) exact direct fragment run by
  `execMixed` = ideal source; (2) PPM-gadget fragment typechecked under the explicit
  ideal-gadget assumption (`execMixed` stuck on the gadget); (3) Library-inspired code
  switch typechecking with its proved symplectic certificate.

## M21 addendum (root-clean layout — no bare `.lean` at the repo root)

Goal: finish M20 by removing the root-level compatibility shims.  The repo root now
contains ZERO bare `.lean` files; every top-level folder owns exactly one PUBLIC
AGGREGATE `<Folder>/Basic.lean`.  Behavior-preserving (only module paths / imports
changed): full `lake build` passes; no `sorry`/`admit`/`native_decide`.

- **Removed** the 10 root files (`Logical.lean`, `Physical.lean`, `PPM.lean`, `PPR.lean`,
  `QStab.lean`, `QClifford.lean`, `ChainQ.lean`, `TypeChecker.lean`, `Compiler.lean`,
  `LogicQ.lean`).
- **Public aggregates** (one per folder): `Logical/Basic.lean`, `Physical/Basic.lean`,
  `PPM/Basic.lean`, `PPR/Basic.lean`, `QStab/Basic.lean`, `QClifford/Basic.lean`,
  `ChainQ/Basic.lean`, `TypeChecker/Basic.lean`, `Compiler/Basic.lean`, and
  `LogicQ/Basic.lean` (the full-pipeline umbrella — imports every layer's `*.Basic`).
- **New import style** (all imports folder-owned + explicit): `import ChainQ.Basic`,
  `import TypeChecker.Basic`, `import Compiler.Basic`, `import PPM.Basic`,
  `import Logical.Basic`, … (or a precise submodule like `import ChainQ.Core.Code`).
  Bare `import ChainQ` / `import PPM` no longer resolve and are forbidden.
- **lakefile.toml**: `roots = ["LogicQ.Basic", "Logical.Basic", "Physical.Basic",
  "ChainQ.Basic", "PPR.Basic", "PPM.Basic", "QStab.Basic", "QClifford.Basic",
  "TypeChecker.Basic", "Compiler.Basic"]`; `defaultTargets = ["LogicQ"]` (the lib).
- **Canonical build**: `lake build` (builds the whole `LogicQ` lib = all roots), or
  per-layer `lake build LogicQ.Basic ChainQ.Basic TypeChecker.Basic Compiler.Basic`.
  (The pre-M21 command `lake build ChainQ TypeChecker LogicQ` referenced the now-deleted
  root modules and is replaced by the `.Basic` targets above.)

POLICY: root-level `.lean` files are intentionally forbidden; per folder, `<Folder>/Basic.lean`
is the public entrypoint and everything else under the folder is an internal module.

## M20 addendum (strict folder-ownership + ChainQ materialization API)

Goal: every real implementation lives in its owning folder; root/shim files carry only
docstrings + imports.  Behavior-preserving (build `ChainQ TypeChecker LogicQ` passes,
8365 jobs; no `sorry`/`admit`/`native_decide`; all examples preserved).

PART A — strict folder-ownership (module PATH moves; NAMESPACES unchanged, so `open`/
qualified names resolve unchanged; old paths become shims/aggregators that re-export):
- **Language layers:** `Logical`/`Physical` whole-file → `Logical/Basic.lean`,
  `Physical/Basic.lean`; `PPM`/`PPR`/`QStab`/`QClifford` gained a `Basic.lean` layer
  (`X.lean` shim → `X/Basic.lean` → `X.Syntax`+`X.Semantics`).
- **TypeChecker judgments:** `Judgment/PPM.lean` → `PPM/{Lift,Certificate,Check,Examples}`;
  `PPMProgram.lean` → `PPMProgram/{DeadSet,State,Check,Soundness,Examples}`;
  `Switch.lean` → `Switch/{Cert,Check,Examples}`; `Transversal.lean` →
  `Transversal/{Cert,Check,Examples}`.  (Switch/Transversal have no soundness ∀-theorems
  — those live in `TypeChecker/Soundness.lean` — so no Soundness submodule.)  The shared
  env fixtures (`q0`/`tenvQ`/`tenvR`/`tenvQR`/`zzCap`) live in `PPM/Examples` and stay
  reachable via the `PPM` aggregator.
- **Compiler:** `Mixed/Lower.lean` → `Mixed/Lower/{Op,Program,ProgramOk,LocMap,Ancilla,
  Public,Examples}` (DAG); `Simulator.lean` → `Simulator/{Arithmetic,State,Gate,
  Algorithms,ExecMixed,Examples}`; `CodeSwitch.lean` → `CodeSwitch/Basic.lean` + shim.
- **ChainQ core/algebra:** `GF2`/`GF2Rank`/`Kernel`/`Shape`/`Ring` → `ChainQ/Algebra/`;
  `Code`/`ChainComplex`/`Params`/`Error` → `ChainQ/Core/`; each old `ChainQ/X.lean` is a
  shim.  (`Params` keeps `import ChainQ.Families` — that cross-edge is a DAG, not a cycle.)
- Top aggregators (`ChainQ.lean`, `Compiler.lean`, `LogicQ.lean`) UNCHANGED; the empty
  `ColorCode/`, `ChainQ2PPR/`, `PPM2LS/`, `QStab2QClifford/` folders stay empty.

PART B — ChainQ materialization / export API (`ChainQ/Materialize/Basic.lean`, namespace
`ChainQ`): `CSSCode.xChecks` (= `hx`), `CSSCode.zChecks` (= `hz`), `CSSCode.checkMatrices`
(= `(hx, hz)`), `CSSCode.symplecticStabilizers` (the width-`2n` rows: X-checks `r ++ 0ⁿ`,
then Z-checks `0ⁿ ++ r`).  The FRONT-END now owns the CSS→stabilizer path: the former
`TypeChecker.cssToStab` is a thin alias `def cssToStab c := c.symplecticStabilizers`
(byte-identical result; `Block.stab` unchanged).  EXACT MEANING: family constructors are
NOT symbolic — for fixed parameters they compute concrete GF(2) matrices (e.g. exact
`surface 2` `Hx`/`Hz`, `surface 2` symplectic = 4 rows × width 10); the "complete
stabilizer set" = the generated `Hx`/`Hz` rows (redundant generators allowed); distance /
fault-tolerance remain OUT OF SCOPE.  Concrete + family smoke tests live in
`ChainQ/Materialize/Tests.lean`.

## M19 addendum (behavior-preserving modular refactor for review)

Goal: put code where it belongs for human reviewability — NO semantic changes, no
new features.  The four monoliths were split into the intended folders; every public
name still resolves through the old module via aggregator/shim re-export, and all
existing tests/examples still pass (`lake build ChainQ TypeChecker LogicQ`, 8319 jobs).

- **ChainQ families →** `ChainQ/HGPCode/{Repetition,Basic}.lean`, `ChainQ/Surface/Basic.lean`,
  `ChainQ/Toric/Basic.lean`, `ChainQ/BBCode/Basic.lean`, `ChainQ/LiftedProduct/Basic.lean`.
  `ChainQ/Families.lean` → aggregator (keeps the 2 inline CSS-condition negative tests).
- **ChainQ checked constructors →** `ChainQ/Checked/Basic.lean` (shared `CheckedCSSCode`/
  `mkCSS`/`mkLogicalBasis` + soundness) and per-family `ChainQ/{Surface,Toric,HGPCode,
  BBCode,LiftedProduct}/Checked.lean` (the `mk*`).  `ChainQ/Checked.lean` → aggregator.
- **Compiler Mixed IR →** `Compiler/Mixed/{Syntax,Check,Source,Lower,Semantics}.lean`
  (DAG: Syntax → {Check, Source}; Lower → {Check, Source}; Semantics → Check — no cycle;
  `progOpNext` moved into `Source` so `Lower` imports it without a back-edge).
  `Compiler/Mixed.lean` → aggregator (Syntax+Check); `Compiler/MixedSemantics.lean` →
  aggregator (Source+Lower+Semantics).
- **Compiler demos →** `Compiler/Demo/{Common,Direct,Algorithms,Frames,Entangling,Families}.lean`;
  `Compiler/Demo.lean` → aggregator.  Shared fixtures (`envN`/`tenv2`/`tenv4`/`demoCfg`/
  `dj2Cfg`/`famCfg`) live in `Demo/Common`.
- **Pass files →** `Compiler/LogicalToQStab.lean` → `Compiler/LS2QStab/Basic.lean` (shim);
  `Compiler/LogicalToPPM.lean` → `Compiler/PPR2PPM/Basic.lean` (shim).  `Compiler/CodeSwitch.lean`
  kept in place (its own `Compiler.CodeSwitch` namespace, cross-cutting external cert layer).
- Top aggregators (`ChainQ.lean`, `Compiler.lean`, `LogicQ.lean`) UNCHANGED — the
  same module names survive as aggregators, so their import lists keep resolving.
- `ColorCode/` and `ChainQ2PPR/`, `PPM2LS/`, `QStab2QClifford/` remain empty (no code
  owns them yet); not part of this split.

## M18 addendum (real operational correctness for the supported fragment)

Goal: turn M17's demo correctness into REAL operational correctness — close the gap
that `loweredGates` decoded `.ppm (.frame q X/Z)` as eager Paulis while the actual
`Step` semantics for a frame only RECORDS it.  Every claim is kernel-checked in
`Compiler/Demo.lean`.

- **Frame semantics made real (task 1).**  Investigation confirmed the PPM `Step.frame`
  rule outputs the carrier UNCHANGED (`⟨ρ,σ,F,.frame q p⟩ → ⟨ρ,σ,F.mulAt q p.toF,.skip⟩`)
  and there is NO frame-propagation through Cliffords — so a record-only lowering was
  operationally a no-op on the carrier (Option B would be wrong without propagation).
  FIX (Option A): new `MixedInstr.pauli (q) (p)` with a `checkInstr` case (live + valid
  operand, like a `.frame`), a new `MixedInterp.pauli : PLetter → LQubit → Q → Q` field
  (a Pauli is NOT a Clifford basis-change, so it cannot route through `clifford`), and a
  `Step.pauli` rule that sets `quantum := I.pauli p q s.quantum` (APPLIES it).
  `xGate`/`zGate` now lower to `.pauli` (not `.ppm (.frame …)`).  Lemmas:
  `Step_pauli_realizes`, `progress_pauli`, and `Step_implies_checkInstr` extended.
- **Operational tests via an executable interpreter (`.pauli` step proven `Step`-aligned) (task 2).**  New
  `Compiler.Sim.simInterp : MixedInterp State` + `execMixed` (executable; `.pauli`
  APPLIES `simInterp.pauli`, `.transversal` applies its Clifford; returns `none`/STUCK
  on anything it cannot run — never silently drops like `loweredGates`/`filterMap`).
  `step_pauli_matches_exec` PROVES `execMixed`'s `.pauli` step is exactly the
  `Step.pauli` carrier update.  `Demo §5` RUNS the emitted programs for `X;H`, `Z;H`,
  `X;S`, DJ-constant through `execMixed` and matches the ideal source — NOT via
  `loweredGates`.  A magic/PPM-gadget program → `execMixed = none` (stuck), contrasted
  with `loweredGates = []` (dropped).
- **Exact fragment classifier (task 3).**  `Demo.exactSupportedOp` marks
  `hGate`/`sGate`/`xGate`/`zGate`/`blockTransversal` exact; `cnotGate`/`czGate`/`tGate`/
  `measure` NOT exact.  `czGate` rides the PLACEHOLDER `progCZAt` → EXPERIMENTAL.
- **Family coverage (task 4).**  `Demo §8` compiles through SURFACE-2 (n=5,k=1, with
  explicit `blocks.length=1`/`n=5`/`k=1` assertions — no silent empty fallback), TORIC-2
  (n=8,k=2), an HGP (`mkHGP (repOpen 3)(repOpen 2) 2 3 1 2`, n=8,k=1), a BIVARIATE-BICYCLE
  (`mkBB 2 2 [(0,0),(1,0)] [(0,0),(0,1)]`, n=8,k=2), and a LIFTED-PRODUCT
  (`mkLiftedProduct 2 [[[0],[1]]] 1 2`, n=10,k=2), each via `mk<Family> →
  cssToTypedBlock? → TypedEnv → compile? → checkLogicalExec` on the exact fragment; the
  k=2 families use a valid index `⟨0,1⟩` and reject out-of-range `⟨0,2⟩`.  `decide`
  feasible to n=10, no `native_decide`.
- **CNOT status made precise (task 5).**  The Bell example renamed to
  `typecheckedCNOTLowering` with an explicit "NOT channel correctness" header; added a
  test that the emitted program has ≥3 PPM `.meas` (nontrivial gadget) AND that
  `execMixed` is `none` (stuck) on it — so no operational CNOT correctness is claimed.
- **Docs (task 6).**  README has the EXACT / IDEAL-CHANNEL / DEFERRED tier table;
  "end-to-end correct" scoped to the exact fragment.

## M17 addendum (honestly end-to-end correct for the supported fragment)

Goal: close the semantic holes that made M16 look stronger than it was — NOT broaden
scope.  Every claim below is kernel-checked by `decide` in `Compiler/Demo.lean`.

- **Pauli-frame semantics fixed (task 1).**  `xGate`/`zGate` lower to a `.ppm (.frame
  q .X/.Z)` byproduct, but the simulator was interpreting the SOURCE as a physical
  Pauli while leaving the EMITTED frame undecoded (a silent source≠emitted gap).
  FIX: `mixedInstrToGate?` now decodes a single-stmt `.ppm (.frame q P)` to the EAGER
  physical Pauli (`X`/`Z` on `L q`).  HONEST because eager-Pauli = deferred-frame in
  FINAL STATE: a Pauli pushed through a Clifford becomes its conjugate (`X;H ≡ H;Z`
  since `HXH=Z`), proved by `decide` (`runGates [X 0,H 0] = runGates [H 0,Z 0]`).
  Now `loweredGates = sourceGates` and run-to-same-state holds for the DIRECT+FRAME
  fragment: `X;H`, `Z;H`, `X;S`, and DJ-CONSTANT source-vs-emitted (Demo §5).
- **Source syntax tightened (task 2).**  `sourceOpOk` now rejects `czGate q q`
  (control=target, like `cnotGate`).  `srcOpOk`'s `blockTransversal` case now checks
  TRUE 2×2 shape (`g.length = 2` AND every row `length = 2`), not just row count.
  Negative tests (Demo §6): `czGate q q`, `1×1` / `2×3` / `3-row` matrices all
  rejected; a well-shaped 2×2 accepted.
- **One entangling op compiles end-to-end (task 3).**  Adapter capability fixtures
  (`zzCap02` for the gadget's `Z⊗Z` on blocks (0,2); `xxCap21` for `X⊗X` on (2,1))
  make the Bell-prep program `H q0 ; CNOT q0 q1` genuinely lower and TYPE-CHECK
  through `compile?` (Demo §7): `sourceWellFormed = true`, `sourceCompilable = true`,
  `compile?` ok, emitted `checkLogicalExec` ok; WITHOUT the caps it is well-formed but
  not compilable.  (The gadget connStab rows were read off `targetPOf`; the ancilla
  block carries 2 logical qubits because the ancilla-address seed advances once per op,
  so the leading `hGate` shifts the gadget ancilla to `⟨2,1⟩`.)  The gadget CHANNEL
  stays an ideal assumption; the COMPILER PATH is real.
- **A real ChainQ family compiles through the compiler (task 4).**  Demo §8 runs the
  full checked pipeline `mkSurface 2 → cssToTypedBlock? → TypedEnv → compile? →
  checkLogicalExec` (distance-2 surface code, `n=5`, `k=1`).  Transversal `H` is
  honestly NOT legal there (`hx ≠ hz` from the repetition hypergraph product), so the
  supported FRAME/MEASUREMENT fragment compiles (`xGate`/`zGate`/`measure`); `decide`
  evaluates through it with no `native_decide`.
- **Docs (task 5).**  README lowering table marks direct `H`/`S` and the symplectic
  fragment EXACT, `X`/`Z` as final-state-exact frame semantics, `CNOT`/`CZ` as
  type-checked gadget lowering with an ideal CHANNEL, and `switch` as Mixed-only /
  external.  Stale `compileMixed?` / `sourceProgramOk` / `ExecutableMixed` references
  in active code comments + the README purged (renamed to `compile?` /
  `sourceWellFormed` / `sourceCompilable`).

## M16 addendum (coherent source language + aligned simulator/compiler)

Goal: make the language design COHERENT and demo-complete — syntax/semantics line up
at each layer; ONE source AST drives BOTH the compiler and the simulator.

- **Unified source language (task 1).**  `LogicalOp` extended with `xGate`/`zGate`
  (Pauli/FRAME ops — lower to `.ppm (.frame q .X/.Z)`, NOT a symplectic basis change)
  and `czGate` (2-qubit Clifford — lowers to the new `progCZAt` gadget, a DEMO
  PLACEHOLDER shaped to type-check; exact CZ measurements + channel correctness
  deferred).  The DJ/Grover/Simon algorithms are now expressible IN the compiler
  source language, not only the simulator `Gate` type.  `compileOp_sound` reproved
  over the new constructors (`propext`,`Quot.sound`).
- **Two-tier source checking (task 2).**  `sourceProgramOk` → renamed
  `sourceWellFormed` (OPERANDS only).  NEW `sourceCompilable mode cfg Γ ops := ok?
  (compile? …)` — strictly stronger (operands PLUS an available lowering).  `compile?`
  checks well-formedness first (clear operand error) then lowers (= compilability
  check).  Theorems: `compile?_sourceOk` (success ⇒ well-formed); `sourceCompilable_
  wellFormed` (compilable ⇒ well-formed).  DEMONSTRATED: `djBalancedSrc` is
  `sourceWellFormed = true` but `sourceCompilable = false` (its `CNOT` needs a
  cross-block adapter capability that is unavailable).
- **Resource syntax (task 3).**  The unused public `CompileConfig.pool` field was
  REMOVED; `CompileConfig` = `caps` + ancilla ADDRESS SEED `anc`.  Resource checking
  (a threaded `ResourcePool` = `AncillaPool`) is explicitly DEFERRED (`alloc`/
  `alloc_valid` remain the checked-allocation primitive for a later pass).
- **Aligned simulator & compiler (task 4).**  ONE source AST: `compile?` lowers it and
  the simulator interprets the SAME `LogicalOp` via `opGate?` (extended: `xGate`→X,
  `zGate`→Z, `czGate`→CZ).  Under the `flat 1` layout (`⟨i,0⟩ ↦ qubit i`),
  `sourceGates djConstantSrc = djConstant` (etc., proved by `decide`).  DJ-CONSTANT
  (`X`+`H` only) FULLY compiles (frame + direct transversal) and the emitted program
  type-checks; the entangling algorithms are simulator-validated at the ideal level.
  The direct H/S/H emitted-vs-source equality is retained.
- **Lowering table (task 5).**  README now has the precise 5-column table (source op →
  typechecker condition → Mixed IR lowering → simulator interpretation → assumption);
  `switch` is marked MIXED-ONLY (not a source `LogicalOp`; a code switch is emitted by
  a pass + carries an EXTERNAL `CodeSwitch` certificate, not written in source).

REGRESSION (task 6): `lake build ChainQ TypeChecker LogicQ` passes; `compile?` rejects
malformed operands AND well-formed-but-unavailable implementations; DJ/Grover/Simon are
`LogicalOp` programs whose ideal semantics validate; the direct H/S fragment still
lowers to direct transversals with source = emitted.  No `sorry`/`admit`/`native_decide`.

## M15 addendum (demo-complete pipeline + unified public compiler)

Goal shift: ACCELERATE toward a clean, demo-complete pipeline (Source → Mixed IR →
PPM/direct/switch/magic → simulator), not maximize proof-carrying.

- **Public soundness bug FIXED + unified API (tasks 1+2).**  ONE public entry
  `compile? : CompileMode → CompileConfig → TypedEnv → List LogicalOp → Except …`
  replaces the M14 split (`compileMixed?` / `compileMixedModuloMagic?` /
  `ExecutableMixed` — removed).  It runs the SOURCE TYPECHECKER `sourceProgramOk`
  FIRST (operand validity via `srcOpOk` — so `hGate ⟨b,99⟩` and other bad logical
  indices are REJECTED, the M14 executable-path hole; CNOT control≠target;
  measurement PPM-legal), then lowers, then applies the mode's magic policy.
  `CompileMode` = `executable` (rejects `.magic` via `progNoMagic`) | `moduloMagic`
  (keeps typed `MagicObligation`s); BOTH modes share the typechecker.  Theorem
  `compile?_sourceOk` (propext): success ⇒ `sourceProgramOk = true`.  Regression
  tests: invalid H/S/T operands and CNOT c=t rejected by `compile?` in both modes.
- **Resources (task 4).**  `CompileConfig` carries a runtime-checked `ResourcePool`
  (= the M14 `AncillaPool`: validity/liveness/basis/ownership); the bare
  `AncillaSupply` address counter is marked INTERNAL (the address generator threaded
  by `compileProgramLocA`).  No new pool theorems (per the brief).
- **Code switching as an EXTERNAL certificate boundary (task 5).**  `CodeSwitch`
  certs reworded to NOT overclaim: `check` → `structuralCheck` (checks
  shape/direction/injectivity-CLAIM only, never correctness/fault-tolerance); a
  strong module disclaimer marks them EXTERNAL/ASSUMED; valid + three invalid switch
  examples (bad shape / non-injective / dishonest-distance) added.
- **Demo (task 6, `Compiler.Demo`).**  The full pipeline on a compilable source
  program `H;S;H`: `compile?` source-typechecks → lowers → emitted Mixed IR
  type-checks → the simulator's run of the EMITTED program equals the source
  circuit (exact, direct fragment) → expected `H S H |0⟩` state.  Plus the algorithm
  set — Deutsch–Jozsa, 2-qubit Grover, Simon n=2 — validated at the IDEAL source-
  semantics level (outcomes by `decide`).  `compile?` rejecting `hGate ⟨0,99⟩` is
  demonstrated.
- **Explicit syntax (tasks 3+7).**  Source ops: `measure`/`hGate`/`sGate`/`cnotGate`/
  `tGate`/`blockTransversal`; Mixed IR: `transversal`/`ppm`/`switch`/`magic`.  The
  README carries the source→Mixed-IR LOWERING TABLE and the DEMO ASSUMPTIONS.

ASSUMPTIONS (stated plainly, per acceptance criteria): direct logical ops + PPM
gadgets are ASSUMED to implement their ideal logical action (the simulator runs that
ideal action, not the physical gadget channel); NO circuit-level distance proof, NO
full fault-tolerance; code-switch certificates are EXTERNAL/ASSUMED unless their
structural shape/direction/injectivity-claim is `structuralCheck`-ed.  (`switch` is a
Mixed-IR op + a `CodeSwitch` certificate boundary, not yet a primitive source op.)

## M8 addendum (compiler start + PPM IR contract)

The fifth pass begins the inter-level COMPILER, after tightening the PPM target
contract so lowering is trustworthy.

- **PPM target policy = STRICT QMeas**: `checkPPM` now enforces `PPM.MTarget.wf`
  (1- or 2-factor logical Pauli, no repeated logical qubit — the native
  lattice-surgery alphabet), rejecting `>2`-factor / duplicate-qubit targets with
  `TypeError.nonNativeMeasurement` (after `emptyMeasurement`). Existing 1-/2-qubit
  measurements (incl. the cross-code `zzTarget`) still pass.
- **PPM program well-formedness** ([TypeChecker/Judgment/PPMProgram.lean](../TypeChecker/Judgment/PPMProgram.lean)):
  `checkPPMStmt` / `checkPPMProgram` over `TypedEnv` — every `.meas` legal via
  `checkPPM`; every `.frame`/`.discard` hits an in-range logical qubit
  (`validLQubit`); every adaptive `.ite` branches on an already-measured outcome
  (classical-variable discipline, `unboundOutcome`). Plus `measTargets` and the
  ∀-theorem **`checkPPMStmt_meas_sound`** (well-typed ⇒ every measurement site
  passes `checkPPM`).
- **First compiler pass** ([Compiler/LogicalToPPM.lean](../Compiler/LogicalToPPM.lean)):
  a small `LogicalOp` language → PPM IR. `measure → .meas`; `hGate/sGate/cnotGate
  → progH/progS/progCNOT`; `tGate → magicObligation` (π/8 deferred until MagicQ).
  `compile?` returns `Except CompileError (CompiledPPM Γ caps)`, where a
  `CompiledPPM` CARRIES `ok? (checkPPMProgram Γ caps stmt) = true`.
- **Compiler soundness** (∀, sorry-free, `propext`-only): `CompiledPPM.wellFormed`
  (the output type-checks), `CompiledPPM.meas_legal` (every emitted measurement is
  legal, via `checkPPMStmt_meas_sound`), and `CompiledPPM.targets_valid` (every
  `frame`/`discard` targets a valid live logical qubit, via
  `checkPPMStmt_targets_valid`).
- **Wiring**: `TypeChecker.lean` re-exports `Core.Elaborate` (+ `Judgment.PPMProgram`);
  `Compiler` is a lakefile root imported by `LogicQ.lean`.
- **Post-review (adversarial pass, 3 low fixed)**: `validLQubit` now also requires
  the block to be LIVE (so `frame`/`discard` reject a consumed block, consistent
  with `meas`); the frame/discard discipline is lifted to the ∀-theorem
  `checkPPMStmt_targets_valid`; and the S-gate gadget is shown to compile AND
  type-check end-to-end through the proof-carrying `compile?` over the two-block
  env `tenvQR` with the joint-`ZZ` adapter `zzCap`.  Still-open low note: the
  classical-variable (`ite`-on-bound-outcome) discipline is enforced
  definitionally + test-covered but not yet lifted to a standalone theorem
  (the dynamic bound-set threading makes a clean statement awkward).

Deferred for the compiler: qubit-parameterized gadgets + capability fixtures so
the H/S/CNOT gadgets (cross-block) type-check end-to-end; ChainQ-family →
`TypedBlock` → program assembly; π/8 lowering once MagicQ lands.

## M9 addendum (mixed logical-execution layer — PPM is NOT the universal target)

**Design shift: PPM is one CHECKED target sublanguage, not the universal compiler
target.**  Transversal gates and code switching are first-class target
instructions and are NEVER compiled into PPM when a cheaper legal direct
operation exists.

- **PPM resource hole fixed** ([PPMProgram.lean](../TypeChecker/Judgment/PPMProgram.lean)):
  `checkPPMStmt` now threads a `PPMState` (bound classical outcomes + DISCARDED
  logical qubits), not just classical vars.  `meas`/`frame`/`discard` reject
  touching a discarded qubit; `discard q ;; frame q` is rejected
  (`useAfterDiscard`).  New ∀-theorems: `checkPPMStmt_dead_mono` (discards
  accumulate) and **`checkPPMStmt_no_use_after_discard`** (a well-typed program
  never references a discarded qubit) — both sorry-free.
- **Parameterized gadgets** ([PPM/Syntax.lean](../PPM/Syntax.lean)):
  `progHAt`/`progSAt`/`progCNOTAt q anc …`; the fixed `progH`/`progS`/`progCNOT`
  are now defeq instances (so `PPM.Semantics` is unchanged).
- **Mixed IR** ([Compiler/Mixed.lean](../Compiler/Mixed.lean)): `MixedInstr` =
  `ppm` | `transversal` | `automorphism` | `switch` | `magic`; `LogicalExec` =
  a list.  `checkInstr`/`checkLogicalExec` dispatch each instruction to its
  TypeChecker judgment and THREAD the `TypedEnv` (a `switch`'s post-switch env is
  seen downstream; use-after-consume rejected).
- **Implementation selection** (`compileOp`, explicit `cost`): for `H`/`S` try a
  DIRECT transversal first, fall back to a PPM gadget only if illegal, else a
  typed error/obligation.  `T` → magic obligation.  A legal transversal `H` on
  the bare qubit is emitted as `.transversal`, verified NOT `.ppm`.
- **Direct-fragment correctness** (∀, sorry-free): `MixedInstr.action` /
  `LogicalOp.srcAction` give the SYMPLECTIC (Heisenberg) action;
  `compileOp_hGate_transversal_sound` / `…_sGate…` prove that an emitted direct
  transversal reproduces the source gate's action.  Honest scope: symplectic-
  level (a Clifford is fixed by its Pauli action up to phase); full unitary-with-
  phase equivalence and a PPM frame-channel semantics are deferred.
- The M8 PPM-only compiler (`LogicalOp`→all-PPM `compile?`) is SUPERSEDED;
  [Compiler/LogicalToPPM.lean](../Compiler/LogicalToPPM.lean) now carries only the
  PPM-fragment evidence `CompiledPPM`.

Post-review (adversarial pass, 5 fixed): (a) `cost` now genuinely DRIVES selection
— `firstLegal` sorts candidates by `cost` (`sortByCost`/`insByCost`), tested by
picking a cheaper transversal over an earlier-listed legal PPM gadget; (b) the
mixed checker threads the PPM resource state (`PPMState`) across instructions, so
use-after-discard is caught ACROSS separate `.ppm` fragments (not just within
one); (c) the switch-threading test is now a genuine discriminator (an `idMat 6`
automorphism is legal only on the n=3 post-switch block, illegal on the n=1
source) — which also exercises the `automorphism` instruction.  Honest remaining
scope: CNOT lowers only to a PPM gadget (transversal CNOT is inter-block, not
expressible by the single-qubit `checkTransversal`), and the source gate set
(H/S) maps to transversals, so `compileOp` never emits an arbitrary
`automorphism` (it is a first-class checkable instruction, used directly in
hand-written mixed programs).

## M7 addendum (typed environment — invalid blocks unrepresentable)

The fourth pass finishes the typed-core integration so that malformed/incomplete
logical blocks cannot exist in the type-checker environment.

- **`Block.valid` completeness** ([Block.lean](../TypeChecker/Core/Block.lean)):
  split into `validPartial` (shape + commutation + pairing + not-in-span) and
  `valid := validPartial && decide (lx.length = n − rank stab)` — the logical
  arity must equal the code dimension `k = n − rank(stab)` (RANK, so redundant
  generators are fine). Partial exposure (gauge fragments) uses the separate
  `SubBlock` (`validPartial`), never a weakened `Block.valid`.
- **`TypedEnv`** ([Block.lean](../TypeChecker/Core/Block.lean)): `List TypedBlock`
  (each carrying `block.valid = true`). All four judgments now take `TypedEnv`
  (and `checkSwitch`'s target is a `TypedBlock`) and NEVER re-check `Block.valid`.
  Malformed blocks enter only through the raw boundary wrappers
  `TypedEnv.ofEnv?` / `checkSwitchFromEnv` / `checkPPMFromEnv`, which validate once
  and reject with `malformedBlock i` / `malformedTarget`.
- **ChainQ→TypeChecker elaborator** ([Elaborate.lean](../TypeChecker/Core/Elaborate.lean)):
  `toTypedBlock? : CheckedCSSCode → CheckedLogicalBasis → Except TypeError TypedBlock`
  (and `cssToTypedBlock?`) — `cssToStab` for stabilizers, CSS logicals embedded as
  `(lx|0)`/`(0|lz)`, runtime-validated. The surface(2) family elaborates to a
  validated symplectic `TypedBlock` (tested).
- **Empty PPM rejected**: `checkPPM []` ⇒ `TypeError.emptyMeasurement` (no
  identity/no-op form).
- **Typed capabilities/certs**: `CheckedCapability` (+`mkCapability?`) carries a
  `connStab`-width-`2·mergedN` proof; `CheckedSwitchCert nC nD` (+`mkSwitchCert?`)
  carries a `2nC×2nD` proof. Target-code failures report `malformedTarget`, not
  the source block id.
- **Unsafe/raw helpers namespaced**: `ChainQ.Internal.{hgp,bb,liftedProduct}`,
  `ChainQ.GF2.Unsafe.{gf2Inv,quotientBasis}`,
  `TypeChecker.Internal.transversalMap` — public code uses the checked
  constructors / typed wrappers.
- **Theorem upgrades** ([Soundness.lean](../TypeChecker/Soundness.lean), ∀, sorry-free,
  axiom-clean): `Block.valid_complete` (extracts `lx.length = n − rank stab`);
  the judgment soundness lemmas restated over `TypedEnv` WITHOUT restating
  `Block.valid` (it is given by the type); `checkPPM_nonempty`; and
  **`checkPPM_merged_sound`** — when a cross-code PPM is accepted via a capability,
  the recomputed merged stabilizer code commutes, contains every lifted data
  stabilizer, and measures the target (the merged-code certificate, not just
  block validity; non-vacuous — the `zzCap` test is a witness).

## M6 addendum (typed core + integration soundness)

The third pass turns "raw record + Bool validator" into a small typed core where
well-formed objects CARRY their validity proof, and the type-checker judgments
reject malformed inputs before any algebra.

- **Validity-carrying code objects** ([Checked.lean](Checked.lean)):
  `CheckedCSSCode` (`code` + `code.valid = true`), `CheckedLogicalBasis`
  (`code` + `basis` + `CSSLogicalBasis.valid code basis = true`). Impossible to
  construct invalid. `TypedBlock` (block + `Block.valid = true`) in
  [TypeChecker/Core/Block.lean](../TypeChecker/Core/Block.lean).
- **`Except`-returning public constructors** ([Checked.lean](Checked.lean)):
  `mkCSS`, `mkSurface`, `mkToric`, `mkHGP`, `mkBB`, `mkLiftedProduct`,
  `mkLogicalBasis` return `Except ChainQError CheckedCSSCode` /
  `CheckedLogicalBasis` with detailed errors (`badDimension`,
  `degenerateParam`, `invalidCSS`, `logicalDerivationFailed`). The raw
  `Families`/`Kernel` builders are kept as internal/unsafe fixtures behind them.
- **`Block.valid`** ([Block.lean](../TypeChecker/Core/Block.lean)): the symplectic
  analogue of `CSSLogicalBasis.valid` — width-`2n` rows, stabilizers commute,
  `k_X = k_Z`, logicals commute with stabilizers, identity symplectic pairing
  (`gemmT lx (lz.map (swapHalves n)) = I_k`), no logical in the stabilizer span.
- **Judgments establish/precheck `Block.valid`**: `checkPPM` rejects any malformed
  touched block (`malformedBlock`); `checkSwitch` requires `Block.valid C` and
  `Block.valid D`; `checkLogicalAutomorphism`/`checkTransversal` require
  `Block.valid blk`. This closes the *zero-width logical* hole (a block with
  `lx = [[]]` was previously measured as trivial identity; now rejected).
- **Certificate shape-checks before algebra**: `SwitchCert.f` must be
  `2·n_C × 2·n_D` (checked before `applyCross`); transversal action stays
  `2n×2n`; `Capability.connStab` rows must be width `2·mergedN` (checked before
  the merged-code span tests).
- **Honest transversal split** ([Transversal.lean](../TypeChecker/Judgment/Transversal.lean)):
  the old `checkTransversal` (an *arbitrary* symplectic automorphism check) is
  renamed **`checkLogicalAutomorphism`**; the new **`checkTransversal`** takes a
  genuinely LOCAL single-qubit `2×2` gate `g` and verifies its tensor power
  `transversalMap n g` (so transversal `H` ⇒ `J n`).
- **Soundness theorems** (∀, not `decide`): `deriveLogicalBasis?_sound`
  ([Params.lean](Params.lean)); `mkCSS_sound`/`mkSurface_sound`/`mkToric_sound`
  (success ⇒ exactly that code, valid); `checkLogicalAutomorphism_sound`,
  `checkTransversal_sound`, `checkSwitch_sound` (now also establishing
  `Block.valid C/D`), and `checkPPM_blocksValid` (success ⇒ no touched block is
  malformed) in [Soundness.lean](../TypeChecker/Soundness.lean).
- **Unsafe algebra namespaced/documented**: `gf2Inv`/`quotientBasis` carry
  ⚠ INTERNAL banners; checked `gf2Inv?`/`quotientBasis?` added
  ([Kernel.lean](Kernel.lean)).

## What was implemented

### 1. Explicit shape algebra — [ChainQ/Shape.lean](Shape.lean)
The review found that `dotBit`/`transpose`/`matMul` and `List.zip`/`getD`
silently truncate/pad, so shape mistakes could pass a Bool check. New explicit
predicates and safe accessors (lightweight Bool style):
- `width`, `height`, **`matrixWellShaped`** (all rows equal length),
  **`hasShape m r c`**, **`sameWidth`**, **`square`**, **`compatibleMul`** (a·b
  shape-compatible);
- **`row?`** — safe row access returning `Option` (out-of-range → `none`, **never
  a silent zero row**); `hcat?`/`vcat?` — checked block concatenation (`none`
  unless row counts / widths match, so `zip` cannot silently drop a row).
- Building blocks for product codes: `identMat`, `zeroMat`, **`kron`** (GF(2)
  Kronecker product), `hcat`/`vcat`.

### 2. Circulant group-ring — [ChainQ/Ring.lean](Ring.lean)
The one new algebraic primitive the lifted-product/BB families need:
`F₂[x]/(xˡ−1)` by exponent support (`Circ`), with `circulant`, `circDagger`
(antipode `x ↦ x⁻¹`), `circMul`, ring-matrix ops (`pIdent`, `pDagger`, `pKron`,
`pHcat`) and the binary lift `liftMat`; plus `shiftPow`/`matXor`/`biCirculant`
for the bivariate ring. Verified law: `transpose (circulant p) = circulant
(circDagger p)` (the fact behind the CSS condition of these families).

### 3. Parametric code families — [ChainQ/Families.lean](Families.lean)
All built from the algebra above (no hardcoded matrices except tiny fixtures),
each checkable by `CSSCode.valid`/`cssCondition`:
- `repOpen`/`repCyc` — classical repetition codes;
- **`hgp`** — hypergraph product `[h1⊗I | I⊗h2ᵀ]`, `[I⊗h2 | h1ᵀ⊗I]`;
- **`surface d`** = `hgp` of two open repetitions (`[[d²+(d−1)², 1, d]]`);
- **`toric d`** = `hgp` of two cyclic repetitions (`[[2d², 2, d]]`);
- **`bb ℓ m a b`** — bivariate bicycle `[A|B]`, `[Bᵀ|Aᵀ]` (`n=2ℓm`);
- **`liftedProduct ℓ A rA nA`** — Panteleev–Kalachev `LP(A,A*)` (`n=(rA²+nA²)ℓ`).
Tests verify `n`, `hasShape` of `hx`/`hz`, and `cssCondition` for small
instances (surface d=2,3; toric d=2,3; BB ℓ=m=3; LP tiny), plus negatives
(anticommuting checks; ragged matrix rejected by `wellShaped`).

### 4. Parameters & logical bases — [ChainQ/Params.lean](Params.lean)
- **`CSSCode.k = n − rank Hx − rank Hz`** — computed from `GF2Rank.rank`, not
  declared. Tested: `surface.k = 1`, `toric.k = 2` (known values).
- **`CSSLogicalBasis.valid`** — checks a *supplied* logical basis with shape
  checks FIRST (so wrong `k×n` is rejected, never zip-truncated): X-logicals ⟂
  Z-stabilizers, Z-logicals ⟂ X-stabilizers, each logical NOT in its stabilizer
  span (genuinely logical), and the symplectic pairing `gemmT lx lz = I_k`.
  Tested on `bareQubit`/`xCheck2` with negatives (wrong width, wrong pairing, a
  stabilizer masquerading as a logical).

### 5. ChainComplex — [ChainQ/ChainComplex.lean](ChainComplex.lean)
`wellShaped` now uses the explicit `hasShape` predicate; chain law `∂₁∘∂₂=0` and
the soundness theorem `chainComplex_css` (chain law ⟺ `Hx·Hzᵀ=0`) are preserved.

## What was deliberately NOT implemented (and why)

- **Explicit lattice cell-complex generator for surface/toric** (`∂₂`/`∂₁` over a
  parameterised 2D lattice, the README `CellComplex` form). Surface/toric are
  instead the HGP of repetition codes — the *same* code, parametric in `d`, and
  the genuine product chain complex. The `ChainComplex` structure still handles
  explicit small cell complexes (`triangle`, `square`). A lattice generator
  needs a lattice-indexing helper; deferred (HGP suffices).
- **Distance `d`** — not computed (NP-hard in general). Only `n` and `k` are
  computed; distance is left as a parameter/obligation. *(Still deferred.)*
- **Co-rank-reduced HGP** (dropping redundant checks) — we use the standard
  full-check Tillich–Zémor form (`valid`, just with redundant rows). *(Still
  deferred — cosmetic.)*
- ~~Derived logical operators for the families~~ — **DONE in M5** via
  `deriveLogicalBasis?` (see addendum).
- ~~TypeChecker `factorRep` fix~~ — **DONE in M5** (`factorRep?` + `checkPPM`
  `badLogicalIndex`; see addendum).

## Minimal language/type-system extensions needed next

1. ~~GF(2) nullspace / kernel-basis finder~~ — **DONE in M5**
   ([Kernel.lean](Kernel.lean)); logicals are now derived, not just checked.
2. A `CSSCode`/`Block` variant carrying an *optional, checked* logical basis (so
   codes can ship verified logicals end-to-end into the TypeChecker), and a
   `ChainComplex`-level product constructor exposing `hgp` as boundary maps
   `∂₂=hx`, `∂₁=transpose hz`.
3. **Distance lower-bounds** (e.g. via the kernel machinery: minimum weight of a
   nontrivial logical) — the remaining unverified code parameter. Exact distance
   is NP-hard, but small-instance/decoder-assisted bounds are feasible.

## Sources informing the formulas
- HGP / surface / toric — Tillich & Zémor, *Quantum LDPC codes…* (arXiv
  0903.0566); chain-complex/tensor view: Audoux (arXiv 1512.07081).
- Lifted product — Panteleev & Kalachev, *…Almost Linear Minimum Distance*
  (arXiv 2012.04068), §4.1–4.3 (conjugate transpose `A* = A(x⁻¹)`).
- Balanced product (background) — Breuckmann & Eberhardt (arXiv 2012.09271).
- Bivariate bicycle — taken from arXiv 2410.03628 (`[A|B]`, `[Bᵀ|Aᵀ]`,
  `x=Sₗ⊗Iₘ`, `y=Iₗ⊗Sₘ`); the canonical Bravyi et al. 2024 paper is **not** in the
  Library, so this is the grounded substitute.

## Pitfalls addressed
- Out-of-range index → zero row: fixed in ChainQ via `row?` AND adopted in the
  TypeChecker (`PPM.factorRep?`, `checkPPM` `badLogicalIndex`) — M5.
- zip/getD/padding silent acceptance: every code/logical/chain validity check is
  gated by an explicit shape predicate (`hasShape`/`wellShaped`/`matrixWellShaped`)
  that returns `false` on a shape mismatch, so a malformed matrix is *rejected*,
  not silently truncated to a passing answer.
- No tautological "soundness": `CSSLogicalBasis.valid` and `cssCondition` check
  genuine algebraic conditions (`orthogonal`, `inSpan`, `gemmT = I`), not the
  same Bool they guard on.
