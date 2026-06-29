# Compiler/CodeSwitch

> Typed, proof-carrying certificates for code switching, dimension jumps, product surgery, and QGPU/qLDPC parallel logic.

This layer sits between the TypeChecker legality kernels and the Mixed IR. It packages the qLDPC-operation paper suite (transversal dimension jump, batched switching, product surgery / QGPU, GPPM) as typed certificates whose GF(2)/symplectic algebra is RECOMPUTED here, while distance, decoders, fault-tolerance, and operational measurement rules stay explicit deferred obligations. Most artifacts are deliberately `externalOnly`: they carry a proof-carrying checker but are NOT `CheckedPrimitive`s and have NO `MixPrim` constructor (see [QLDPCStatus.lean](QLDPCStatus.lean)). The one method that lowers to MixIR is high-weight capability PPM, admitted through a `CapabilityWitness` whose merged-code certificate `checkPPM` recomputes.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Certificate skeleton: `PhysMap`, `ChainMapCert`, `ChainMapSquare`, `LogicalInjectionCert`, `HomomorphicCNOTCert`, `SwitchProtocolCert`; structural + recomputed (`verifiedCheck`) checks. |
| [DimensionJump.lean](DimensionJump.lean) | Proof-carrying transversal dimension jump: commuting chain square + transversal, non-degenerate `γ₁` + injective induced map; `checkDimensionJump?` + soundness. |
| [ProductSurgery.lean](ProductSurgery.lean) | Product-surgery / QGPU merged CSS code, recomputed CSS-commutation + merge count; `CapabilityWitness` provenance so `.productSurgery` flows only from a `CheckedProductSurgery`; **`CheckedProductSurgeryFor Γ blockId`** binds the cert's `hX/hZ` to the addressed block's CSS extraction (`extractHX`/`extractHZ` over the symplectic `Block.stab`) + `toWitness` authorization. |
| [QGPUAddr.lean](QGPUAddr.lean) | QGPU clustered logical basis + merge-alignment/round legality BOUND to a `TypedEnv`; ChainQ-name re-resolution (`checkQGPURoundIn?`). |
| [BatchedSwitch.lean](BatchedSwitch.lean) | Batched code switching as a `(block,logical) ↦ (logical,block)` transpose route over `LQubit`; env-bound `checkBatchedCodeSwitchFor?` + routing-preservation theorem. |
| [GPPMSemantics.lean](GPPMSemantics.lean) | Generalized PPM: recomputes merged-CSS + target-measured + type-checked byproduct frame; explicitly NOT a `CheckedPrimitive`. |
| [QLDPCPapers.lean](QLDPCPapers.lean) | Paper-shaped protocol wrappers (homomorphic CNOT, GPPM, dimension jump, batched, high-rate surgery) over the checked kernels. |
| [QLDPCStatus.lean](QLDPCStatus.lean) | The honest MixIR-status registry: which methods lower to MixIR vs. are external checked artifacts (`not_all_lower_to_mixIR`). |

(Subdirectory [QLDPCPapers/](QLDPCPapers) — `ChainQProgram.lean`, `Concrete.lean`, `Verification.lean` — holds concrete BB/toric instances; it uses `native_decide` and has no README of its own.)

## Key definitions

```lean
structure SwitchProtocolCert where
  srcBlock        : Nat
  tgtBlock        : Nat
  chain           : ChainMapCert
  injection       : LogicalInjectionCert
  disjointFromOthers : Bool                  -- safe to run in parallel with its batch
  deferred        : SwitchFaultObligations
  distance        : Option DistanceObligation := none
```

```lean
structure DimensionJumpChecked where
  square        : ChainMapSquare
  induced       : LogicalInjectionCert
  squareComm    : square.verifiedCheck = true
  transversal   : square.highMap.physicallyTransversal = true
  nondegenerate : decide (rank square.highMap.matrix = square.highMap.srcN) = true
  injective     : induced.computableInjective = true
  claimedOk     : induced.claimedInjective = true
  dimCompat     : inducedDimCompat square.highMap induced = true
  obligations   : List String
```

```lean
def checkProductSurgery? (c : ProductSurgeryCert) (maxMerge : Nat) :
    Except TypeError CheckedProductSurgery
```

```lean
theorem checkProductSurgery?_sound (c : ProductSurgeryCert) (maxMerge : Nat)
    {r : CheckedProductSurgery} (h : checkProductSurgery? c maxMerge = .ok r) :
    orthogonal c.hX c.hZ = true ∧
      orthogonal c.mergedHX c.mergedHZ = true ∧
      (vcat c.hZ (ChainQ.GF2.zeroMat c.hZ.length c.n)).all
        (fun row => inSpan c.mergedHZ row) = true ∧
      r.merges = rank c.hZ'
```

```lean
theorem not_all_lower_to_mixIR :
    qldpcRegistry.all (fun s => s.status == .lowersToMixIR) = false
```

## Example

A `BatchedCodeSwitchSpec` IS the route data. The canonical 2×2 batched switch
([BatchedSwitch.lean:101](BatchedSwitch.lean#L101)):

```lean
-- a 2×2 batched switch: k1 = k2 = 2; sources = {⟨0,0⟩,⟨0,1⟩,⟨1,0⟩,⟨1,1⟩}.
def bcs22 : BatchedCodeSwitchSpec :=
  { k1 := 2, k2 := 2, sources := [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], dummies := [] }
-- OK: 4 = k1·k2 active logicals, all in range (blk < 2, idx < 2), route is collision-free.
```

Its `routeMap` is the literal `(block j, logical i) ↦ (block i, logical j)` transpose —
the carrier-name lookup as DATA (`LQubit` written `⟨blk, idx⟩`):

```lean
-- bcs22.routeMap : LocMap = the active sources paired with their transposed targets:
[ (⟨0,0⟩, ⟨0,0⟩)      -- diagonal fixed
, (⟨0,1⟩, ⟨1,0⟩)      -- block 0, logical 1 ↦ block 1, logical 0
, (⟨1,0⟩, ⟨0,1⟩)      -- block 1, logical 0 ↦ block 0, logical 1
, (⟨1,1⟩, ⟨1,1⟩) ]    -- diagonal fixed
```

Other spec values, accepted or rejected by the routing well-formedness discipline
(`BatchedCodeSwitchSpec.wf`, [BatchedSwitch.lean:64](BatchedSwitch.lean#L64); negatives from
§BCS.4):

```lean
{ k1 := 2, k2 := 2, sources := [⟨0,0⟩, ⟨0,1⟩, ⟨1,0⟩, ⟨1,1⟩], dummies := [] }   -- OK: the bcs22 route above
{ k1 := 2, k2 := 2, sources := [⟨0,0⟩, ⟨0,1⟩, ⟨1,0⟩, ⟨1,1⟩], dummies := [2,3] } -- OK: dummies out of source-block range, distinct
{ k1 := 2, k2 := 2, sources := [⟨0,0⟩],                       dummies := [] }   -- rejected: 1 ≠ k1·k2 active logicals
{ k1 := 2, k2 := 2, sources := [⟨0,0⟩, ⟨0,1⟩, ⟨1,0⟩, ⟨5,1⟩],  dummies := [] }   -- rejected: source block index 5 ≥ k2
{ k1 := 2, k2 := 2, sources := [⟨0,0⟩, ⟨0,1⟩, ⟨1,0⟩, ⟨1,1⟩], dummies := [2,2] } -- rejected: duplicate dummy ids
{ k1 := 2, k2 := 2, sources := [⟨0,0⟩, ⟨0,1⟩, ⟨1,0⟩, ⟨1,1⟩], dummies := [0] }   -- rejected: dummy collides with active source block (0 < k2)
{ k1 := 2, k2 := 2, sources := [⟨0,0⟩, ⟨0,0⟩, ⟨1,0⟩, ⟨1,1⟩], dummies := [] }   -- rejected: ⟨0,0⟩ twice → route collision (Nodup fails)
```

A well-formed batched code switch routes the `(block j, logical i)` address to its transpose
`(block i, logical j)`. Source: [BatchedSwitch.lean](BatchedSwitch.lean) (§BCS.4 tests).

## Status & scope

Honest, mirroring the repo's contract tiers (P proved theorem, D `by decide` test, A documented assumption, M missing/planned):

- **Recomputed over GF(2) (P/D).** Chain-square commutation (`∂φ = φ∂`), physical transversality + non-degeneracy of `γ₁`, switch/square map coherence (`switch.chain.map = square.highMap`), induced-logical-map injectivity (rank), disjoint-image parallelism (COMPUTED from `physMapImageRows`, not caller-supplied), merged-code CSS-commutation, data-stabilizer preservation, merge count `M = rank H_Z'`, batched-route well-formedness/transpose, QGPU basis/alignment/round legality, AND the **CSS extraction binding** of a product-surgery cert to an addressed block (`CheckedProductSurgeryFor`). These carry `by decide` tests and `*_sound` theorems (e.g. `checkDimensionJump?_sound`, `checkProductSurgery?_sound`, `checkProductSurgeryFor?_sound`, `checkQGPURoundIn?_sound`, `checkBatchedCodeSwitchFor?_preservesRoute`). Soundness theorems are the usual `propext`-clean style, NOT "axiom-free".
- **Provenance (P).** `CapabilityWitness` closes the `.productSurgery` bypass: a `.productSurgery` authorization can only come from a `CheckedProductSurgery` (`generic_not_productSurgery`, `genericWitness?`).  A `CheckedProductSurgeryFor` additionally binds that cert to the addressed `TypedEnv` block (cert `hX/hZ` = the block's CSS extraction) and AUTHORIZES the witnessed PPM via `toWitness` (`checkProductSurgeryFor?_sound`, `toWitness_kind`).
- **Block-identity binding (P, NEW).** `CheckedProductSurgeryFor Γ blockId` resolves `blockId` in `Γ`, requires the block CSS (`blockStabIsCSS`), and proves the cert's data code `(hX, hZ)` IS the CSS extraction (`extractHX`/`extractHZ`, convention pinned to `Symplectic`: `take n` = X-half, `drop n` = Z-half) of the block's symplectic `Block.stab`.  Tests: matching cert accepted; different `hX/hZ`, SWAPPED X/Z (still a valid CSS code, but rejected by the binding), wrong block id, and non-CSS/mixed-row blocks all rejected.
- **Deferred / external / assumed (A/M).** Merged-/jumped-code DISTANCE, decoder thresholds, circuit-level fault distance, one-bit-teleportation init/measurement/feedback, the homology-quotient refinement of injectivity, the operational measurement-outcome rule (no `Step` semantics), and ancilla state preparation are all EXPLICIT deferred obligations (recorded as `obligations : List String`). A `GPPMArtifact` is deliberately NOT a `CheckedPrimitive`.
- **MixIR status (P).** Only high-weight capability PPM lowers to MixIR; the other six methods are `externalOnly` (`not_all_lower_to_mixIR`, `only_ppm_lowers`).  Product surgery is now `Block`-identity-bound (`CheckedProductSurgeryFor`, `productSurgery_blockBound_anchor`) and AUTHORIZES the witnessed PPM, but does not itself lower to a `MixPrim`; QGPU/GPPM/dimension-jump/batched-switch remain first-class protocol nodes (QGPU/dimjump/BCS *could* lower to `parallelPPM`/`codeSwitch`+cert once source syntax + elaboration is wired — NOT done; GPPM CANNOT lower, its outcome=±1 eigenvalue rule has no `Step` semantics).
- The `QLDPCPapers/` concrete instances use `native_decide` (out of the M23 axiom-clean scope).

## See also

- [../README.md](../README.md) — the Compiler layer overview.
- [../CONTRACT.md](../CONTRACT.md) — the full correctness-boundary matrix (tier definitions).
- [../../README.md](../../README.md) — repository root.
