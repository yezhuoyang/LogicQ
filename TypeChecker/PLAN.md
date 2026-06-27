# ChainQ Type Checker — Plan

*A proof-carrying capability matcher for legal logical operations (transversal gates, code
switching, cross-code PPM). Grounded in the `Library/` corpus (qLDPC surgery, code switching,
homomorphic measurement, universal adapters, QIR/ownership types) and built on the existing
`ChainQ.GF2` / `ChainQ.Code` / `ChainQ.ChainComplex` / `Logical` / `PPM` kernel.*

## 0. Thesis

The type checker does **not** ask "is this operation syntactically well formed?" It asks:

> **"Can this requested logical operation be elaborated into *one certified implementation path*?"**

Each judgment returns **evidence**, not a boolean:

```lean
checkTransversal : Env → CliffGate → List BlockId → Except TypeError (TypedTransversal …)
checkSwitch      : Env → BlockId → CSSCode → CSSCode → SwitchCert → Except TypeError (TypedSwitch …)
checkPPM         : Env → MTarget → Except TypeError (TypedPPM …)
checkConsume     : Env → ConsumeOp → BlockId → Except TypeError Env'
```

Each `Typed*` value bundles three things, kept strictly separate:

| Tier | What | When | Example |
|---|---|---|---|
| **Hard checks** | decidable shape/state facts | now, fail-fast | dimensions, CSS validity, liveness, logical-index bounds, Pauli commutation, stabilizer preservation, symplectic-action well-formedness |
| **Certificate checks** | recompute a *compact algebraic witness* supplied with the capability | now | orthogonal symplectic matrix, chain map (`∂f = f∂`), merged-CSS condition, adapter cycle-basis (`N·inc=0`), induced logical map, mapping-cone inclusions |
| **Proof obligations** | heavy facts, **never silently discharged** | deferred (named hypotheses, à la FormalRV's `VerifiedShorOnCode`) | code distance, fault distance (`R≥d` rounds), decoder threshold, Cheeger β / soundness ρ, hardware schedule, postselection rate |

**Mantra:** *do not rediscover physics — verify compact algebraic witnesses.* Every certificate
recomputation is a thin composition of the existing GF(2) primitives (`dotBit`, `transpose`,
`gemmT`, `matMul`, `orthogonal`, `isZeroMat`, and the bridge lemma `zero_gemmT_iff_orthogonal`).

---

## 1. The typing environment Γ

A `Block` is a logical block layered over the existing kernel; `Env` is the finite map + capability
table that the judgments thread (liveness/ownership transitions are functional updates returning `Env'`).

```lean
abbrev CodeRef := CSSCode ⊕ StabilizerCode ⊕ ChainComplex     -- all from ChainQ.*

structure LogicalBasis where        -- the normalizer N(S)/S generators (Gottesman, quant-ph/9705052)
  n  : Nat                          -- physical qubits
  k  : Nat                          -- logical qubits
  lx : BoolMat                      -- k rows in F2^{2n}: logical X̄ᵢ symplectic vectors
  lz : BoolMat                      -- k rows in F2^{2n}: logical Z̄ᵢ symplectic vectors
  -- wf: symplectic Gram of (lx‖lz) is the standard form J (X̄ᵢZ̄ᵢ anticommute, else commute)

inductive Owned | owned | borrowed

structure Block where
  codeId : Logical.BlockId
  code   : CodeRef
  basis  : LogicalBasis
  live   : Bool                     -- QIR allocation-list membership (2303.14500)
  own    : Owned                    -- Guppy ownership (2510.13082)

structure Env where
  blocks : List Block               -- BlockId ⇒ Block (with live/own state)
  caps   : List Capability          -- the installed proof-carrying capabilities
  store  : List Logical.BlockId     -- consumed/retired set (post measure / discard / switch)
```

All matrices are `ChainQ.GF2.BoolMat`. The **symplectic form** lives in one place
(`TypeChecker/Core/Symplectic.lean`): Paulis are doubled vectors `(a‖b) ∈ F2^{2n}`,
`sympForm (a‖b) (c‖d) = dotBit a d ⊕ dotBit b c`, and a Clifford's logical action is a `2n×2n`
`BoolMat M` with "preserves the symplectic form" = `M·J·Mᵀ = J` (checked by `gemmT`).

---

## 2. Capabilities — PPM legality moves out of `MTarget.wf`

`PPM.MTarget.wf` currently checks only arity + no-duplicates. That legality check is **superseded**:
a logical Pauli measurement typechecks only if `Env.caps` exposes a `Capability` whose shapes and
**measurement domain** match, and whose witness the checker re-verifies.

```lean
inductive Capability
  | nativePPM            (shape : CodeShape)    (cert : MeasDAGCert)
  | transversal          (gate  : CliffGate)    (cert : SymplecticCert)
  | codeSwitch           (src dst : CSSCode)    (cert : SwitchCert)
  | adapterPPM           (src dst : CSSCode) (shape : MeasShape) (cert : AdapterGraphCert)
  | productSurgery       (shape : ProductShape) (cert : MergedCSSCert)
  | homomorphicMeasurement (shape : HomShape)   (cert : HomGadgetCert)
  | batchedSwitch        (batchShape : BatchShape) (cert : MeasDAGCert)
```

| Capability | Certificate the checker recomputes | Deferred obligations | Papers |
|---|---|---|---|
| `transversal` | `A` orthogonal in O(n,Z₂) (distinct-row `dotBit=0`, self-dot `1`); `M·J·Mᵀ=J`; stabilizers→stabilizers (row-space membership of `M·g`); induced logical map = request mod stabilizers | FT needs `d>1`; CSS-CNOT distance `≥ min(d₁,d₂)`; small `Aut(S)` | 9705052, 0406196, 2409.13465 |
| `nativePPM` | `Pᵢ` pairwise `sympForm=0` (commute) across branches; each `Pᵢ` is a logical op | adaptive-outcome correctness; stabilizer-rank `χ(H)^m`; FT syndrome extraction | 1506.01396, 9705052 |
| `codeSwitch` | per kind: gauge-fix `GF=0` + merged-CSS `orthogonal`; teleport/dimension-jump commuting squares `∂ᴰf = f∂ᶜ` + induced `γ̄₁` injective (Künneth); one-way-CNOT stabilizer preservation; `φ` = induced map | `d_D`, fault distance (`R≥d`), single-shot / small-set-flip threshold, postselection rate | 2409.13465, 2510.08552, 2603.15610, 2510.06760, 2510.07269, 1512.07081 |
| `homomorphicMeasurement` | row-space inclusions `rs(H_Z Γᵀ) ⊆ rs(H_Z)`, `rs(H_X Γ) ⊆ rs(H_X')`; **or** mapping cone `H̃` with `f₀∂₁ = H_Z f₁` and `dim(ker ∂₁)=1` | X-distance via Cheeger `h≥1`; Z-distance preserved; ancilla Shor prep; decoder unchanged | 2211.03625, 2410.02753, 2410.02213 |
| `productSurgery` | merged block matrices `[H_X,0; H'_X,H_X']` / `[…]` satisfy `orthogonal(mergedHX, mergedHZ)`; chain maps `Γ₀∂ = ∂Γ₀`; `rank(H'_Z) = #merges` | merged distance (Künneth/numerical); soundness `ρ`; schedule; merged decoder | 2407.18490, 2510.08523, 1512.07081, 2012.09271 |
| `adapterPPM` | AuxGraph desiderata 0–3 (connectivity, O(1) degree, cycle basis `N·inc=0`, perfect-matching support); `A_v`,`B_c` commute with deformed checks | relative expansion `β_d ≥ 1` (often needs thickening `L=O(log³n)`); fault distance `=d`; merged decoder | 2410.03628, 2407.18393, 2503.10390 |
| `batchedSwitch` | batch-size `nBlocks = Ω(d²)` (decidable `≥`); BCS routing grid; measurement DAG pairwise-commuting per round + across the adaptive tree; classical LDPC check full-rank | constant space-time overhead; classical-code expansion; merged/BSE decoder; magic-state marginal error | 2510.06159, 1506.01396, 1209.2426 |

**Certificate record types** (`TypeChecker/Capability/Certs.lean`), each with a decidable
`verify : Cert → Bool` built from GF(2)/ChainComplex reuse:
`SymplecticCert` · `ChainMapCert` (`isZeroMat (matMul ∂ f ⊕ matMul f ∂)`) · `MergedCSSCert`
(`orthogonal mergedHX mergedHZ`, soundness via reused `chainComplex_css`) · `AdapterGraphCert`
(`N·inc=0` via `gemmT`) · `HomGadgetCert` (row-space inclusions) · `MeasDAGCert` (pairwise `sympForm=0`).

---

## 3. The judgments

- **`checkTransversal`** *(Milestone 1 — the easiest useful one, pure symplectic matrix algebra)*.
  Hard: blocks live & owned/borrowed; common shape `n`; gate's `M` is `2n`-wide; stabilizers→stabilizers;
  source generators commute. Cert: `A` orthogonal (O(n,Z₂)); `M·J·Mᵀ=J`; induced action = request mod
  stabilizers. Obligations: `d>1`, CSS-CNOT distance.
- **`checkSwitch`** *(Milestone 2 — typed coercion `Block C → SwitchCert C D φ → Block D`)*. Hard: source
  **owned & live** (switching **consumes** — a borrowed block cannot switch); `D` is `CSSCode.valid`;
  `φ` arity `k_C = k_D`; byproduct is a total frame map. Cert: per protocol kind (gauge_fix | teleport |
  dimension_jump | adapter | batched) verify the chain map / GF=0 / merged-CSS; induced map `= φ`.
  Obligations: `d_D`, fault distance, single-shot decoder, postselection rate.
- **`checkPPM`** *(Milestone 3 — the capability matcher)*. Hard: every `LQubit` in `P` references a live
  block; no duplicate qubit (the surviving part of old `MTarget.wf`); each factor a genuine logical op.
  Cert: **search `Env.caps`** for a capability matching `P`'s shapes + measurement domain, then recompute
  that capability's witness. **If none matches across domains → the surface/LP rejection.**
- **`checkConsume`** *(used by Switch + destructive PPM)*. Ownership/liveness transition: destructive
  measure/discard/switch require `owned & live`; on success move the block to `Env.store`, set
  `live := false`; no-leak (every owned live block must be consumed by program end), no-clone (a BlockId
  is not aliased across two live owners).

---

## 4. The driving example: PPM between a Surface-code and an LP-code qubit

`checkPPM Γ [(⟨surf,0⟩, .Z), (⟨lp,0⟩, .Z)]`, `surf` = surface code (domain = surface/MWPM),
`lp` = lifted-product code (domain = qLDPC/BPOSD).

- **Hard checks pass** (both live, distinct qubits, each `.Z` a logical op of its own code).
- **Capability matching fails**: no `nativePPM` covers both domains (the two logical `Z`s live in
  *different chain complexes* with no shared stabilizer group / boundary map); no `adapterPPM` connects
  them; no `codeSwitch` path is installed.
- **Rejection:** `TypeError.noCommonCapability "no native PPM, no adapter, no switch path: blocks surf
  (domain=surface) and lp (domain=qLDPC) share no measurement domain and no installed Capability bridges
  them"`.

It passes **only** through exactly one installed witness:

1. **Switch-then-native** — install `codeSwitch(surf, lp', SwitchCert{kind := dimension_jump, …})`; the
   checker verifies `∂ˡᵖ∘f = f∘∂ˢᵘʳᶠ` (commuting squares; 2510.07269 transversal dimension jump,
   `γ̄₁` injective via Künneth), produces `Env'` with `surf` **consumed**, then `checkPPM` matches an
   LP-domain `nativePPM`/`productSurgery`.
2. **Adapter-domain PPM** — install `adapterPPM(surf, lp, …, AuxGraph{inc, port f, cycleBasis N, …})`;
   verify desiderata 0–3 (`N·inc=0`, bounded degree, connectivity) + relative expansion `β_d≥1`
   (2410.03628). Obligations: `β_d≥1`, thickening, merged decoder.
3. **Teleportation bridge** — install a bridge-kind `adapterPPM` (2407.18393 bridge system / 2503.10390
   EAC bridge): `d` bridge edges with a repetition-code bridge check, verified by recursive bridging.

---

## 5. Ownership & liveness (linear logical resources)

Each `Block` carries `live` (QIR allocation list, 2303.14500) and `own` (Guppy, 2510.13082).
**Non-consuming** ops (transversal Cliffords, gate application) require `live` and `owned`/`borrowed`,
and return the same `Env`. **Consuming** ops (destructive PPM readout, `discard`, `switch`) require
`live ∧ owned` (a *borrowed* block cannot be consumed) and move the BlockId to `Env.store`, setting
`live := false` — so any later reference fails the hard liveness check (use-after-release). **No-clone:**
a BlockId is not aliased across two live owned blocks. **No-leak:** every owned, still-live block must be
consumed by program end (else `TypeError.leak`).

---

## 6. Module layout (`TypeChecker/`)

```
TypeChecker/Core/Symplectic.lean     -- 2n-doubled symplectic layer over GF2: sympForm, J, preservesSymp, isOrthogonalO
TypeChecker/Core/LogicalBasis.lean   -- N(S)/S generators {n,k,lx,lz}; actBy, equalModStabilizers, inLogicalSpan
TypeChecker/Core/Block.lean          -- Block, CodeRef, Owned, CodeShape (n, family, measurement-domain)
TypeChecker/Core/Env.lean            -- Env {blocks, caps, store}; lookup/consume/installCap; no-clone/no-leak
TypeChecker/Core/Error.lean          -- TypeError inductive (incl. noCommonCapability — the surface/LP message)
TypeChecker/Capability/Defs.lean     -- Capability (7 variants) + capMatches over measurement-domains
TypeChecker/Capability/Certs.lean    -- the Cert records + decidable verify (all GF2/ChainComplex reuse)
TypeChecker/Judgment/Transversal.lean-- checkTransversal + TypedTransversal     [M1]
TypeChecker/Judgment/Switch.lean     -- checkSwitch + TypedSwitch + SwitchCert    [M2]
TypeChecker/Judgment/Consume.lean    -- checkConsume (ownership/liveness)         [M2]
TypeChecker/Judgment/PPM.lean        -- checkPPM (capability matcher); supersedes MTarget.wf legality [M3]
TypeChecker/Soundness.lean           -- cert-ok ⇒ algebraic witness holds (analog of chainComplex_css)
TypeChecker.lean                     -- umbrella; add `TypeChecker` to lakefile roots
```

---

## 7. Milestones

| | Goal | Deliverable | Papers |
|---|---|---|---|
| **M0** scaffold + Γ | `Core/` over the GF2 kernel; no new physics | `Symplectic`/`LogicalBasis`/`Block`/`Env`/`Error`; `decide` smoke tests; lakefile root | — |
| **M1** transversal | `checkTransversal`: orthogonal symplectic matrix, stabilizers→stabilizers, induced action mod stabilizers, `J`-preservation | `Judgment/Transversal.lean`; transversal-H / CSS-CNOT on `five_qubit`/`square` by `decide`; soundness `ok ⇒ isOrthogonalO ∧ preservesSymp` | 9705052, 0406196, 2409.13465 |
| **M2** code switch | `checkSwitch` typed coercion, consuming the source; chain-map / merged-CSS / GF=0 certs | `Switch.lean` + `Consume.lean`; reuse `chainComplex_css` to certify the merged/gauge-fixed complex; `[[8,3,2]]` gauge-fix + Steane↔Tetrahedral one-way-CNOT examples | 2409.13465, 2510.08552, 2603.15610, 2510.06760, 2510.07269, 1512.07081, 2303.14500, 2510.13082 |
| **M3** cross-code PPM | `checkPPM` capability matcher; the 7 variants + cert recomputers; the surface/LP rejection + 3 witnesses | `Capability/{Defs,Certs}.lean` + `PPM.lean`; supersede `MTarget.wf`; surface↔LP tests by `decide` | 2410.03628, 2407.18490, 2211.03625, 2410.02753, 2503.05003, 2510.08523, 2510.06159, 1506.01396 |
| **M4** soundness + obligations | soundness theorems (analog of `chainComplex_css`); obligation records wired for downstream FT verification | `Soundness.lean`; `obligations : List Obligation` in every `Typed*`; hook for symbolic FT discharge | 2501.14380 |

---

## 8. Reuse & what to add

**Reused verbatim.** `ChainQ.GF2` — `BoolVec`/`BoolMat`, `dotBit` (the symplectic inner product),
`transpose`, `gemmT`, `matMul`, `isZeroMat`, `orthogonal`, and **`zero_gemmT_iff_orthogonal`** (the
backbone of *every* certificate recomputation). `ChainQ.Code` — `CSSCode`/`StabilizerCode` + validity +
`commutes` + the `five_qubit` fixture. `ChainQ.ChainComplex` — `chainLaw`, `toCSS`, and the headline
**`chainComplex_css`**, reused to certify that merged / cone / gauge-fixed complexes are genuine CSS
codes (M2/M3 cert soundness mirrors it). `Logical.LQubit`/`BlockId`. `PPM.MTarget`/`FPauli`/`Sign`.

**Must add (kept Mathlib-free).**
- a **2n-doubled symplectic layer** (`sympForm`, `J`, `preservesSymp`, `isOrthogonalO`) on top of GF2;
- `LogicalBasis` (normalizer generators) — not in the kernel today;
- `Env` with liveness/ownership;
- the `Capability` inductive + `Cert` verifiers (thin compositions of GF2/ChainComplex);
- **GF(2) rank / row-reduction** (a small Gaussian elimination over `Bool`) — needed for row-space
  membership (stabilizer preservation, `rs(H_ZΓᵀ)⊆rs(H_Z)`), cycle-basis dimension, `dim(ker ∂₁)=1`,
  and induced-map injectivity. **This is the one genuinely new kernel primitive**; unit-test against
  known codes, keep matrices small in `decide` tests.

---

## 9. Risks

1. **No GF(2) rank yet** — adapter cycle-basis dim, `dim(ker ∂₁)=1`, injectivity, and stabilizer-preservation
   membership all need a Mathlib-free Gaussian elimination over `Bool`. *Mitigate:* implement `gf2Rank`/`rowReduce`
   in `Core`, unit-test, keep test matrices small (`decide` performance).
2. **Relative expansion / Cheeger `β_d≥1` is NP-hard** in general — cannot be a hard or cert check.
   *Mitigate:* default to a deferred **obligation**; offer a decidable bounded-witness cert only for
   small/structured graphs (2410.03628: desiderata 0–3 are the decidable LDPC part; (4) is the hard part).
3. **Measurement-domain tagging** (surface vs qLDPC vs LP) is a design choice — too coarse rejects legitimate
   native PPMs, too fine never matches. *Mitigate:* derive the domain from code family + canonical-basis
   structure, not an ad-hoc enum.
4. **Symplectic 2n-doubling layout** must be consistent everywhere or wrong commutation passes silently.
   *Mitigate:* one `Symplectic.lean` owns the layout + `decide` tests pinning `X̄Z̄` anticommutation.
5. **Chain-map basis mismatch** — supplying boundary maps as raw `BoolMat` risks coincidental dimension
   agreement. *Mitigate:* pair every chain map with explicit source/target `ChainComplex` shapes; shape
   agreement is a hard precheck before the cert check.

---

## 10. Open design questions (need a decision; mostly bite at M3, not M0/M1)

1. **LogicalBasis: declared or derived?** Declared (user supplies `lx`/`lz`, checker verifies the symplectic
   Gram) is cheaper and unblocks M1 immediately; derived (compute logicals from the code via the new GF2
   kernel) removes a trust surface but needs a logical-operator finder. *Recommendation: declared first.*
2. **Measurement-domain granularity** — surface vs general-qLDPC vs LP-over-`F2[G]` vs HGP-grid vs
   CC-cluster. This sets the matcher's pass/fail boundary.
3. **Cert vs obligation boundary for expansion** — ever recompute `β_d` for bounded graphs, or always defer?
4. **Destructive vs non-consuming (gauging) measurement** — one judgment with an owned/borrowed branch, or two?
5. **Adaptive PPM tree** — verify pairwise-commuting across *all* branches (exponential) or defer branch
   commutativity to an obligation?
6. **LP / balanced-product representation** — unfold to binary circulant `BoolMat` at declaration (keeps GF2
   reuse, loses cluster/grid structure that `productSurgery`/`batchedSwitch` rely on), or carry ring structure?

---

*Survey basis: a 10-cluster parallel read of the `Library/` corpus (stabilizer/symplectic foundations,
homomorphic measurement, homological-product parallel logic, qLDPC surgery/bridges, universal adapters,
code switching, gauging/dimension-jump/batched, product-code algebra, QIR/ownership types, FT
verification) + the existing LogicQ kernel + the project owner's capability-matcher brief.*
