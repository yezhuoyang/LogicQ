# Compiler/CodeSwitch

> Typed, proof-carrying certificates for code switching, dimension jumps, product surgery, and QGPU/qLDPC parallel logic.

This layer sits between the TypeChecker legality kernels and the Mixed IR. It packages the qLDPC-operation paper suite (transversal dimension jump, batched switching, product surgery / QGPU, GPPM) as typed certificates whose GF(2)/symplectic algebra is RECOMPUTED here, while distance, decoders, fault-tolerance, and operational measurement rules stay explicit deferred obligations. Most artifacts are deliberately `externalOnly`: they carry a proof-carrying checker but are NOT `CheckedPrimitive`s and have NO `MixPrim` constructor (see [QLDPCStatus.lean](QLDPCStatus.lean)). The one method that lowers to MixIR is high-weight capability PPM, admitted through a `CapabilityWitness` whose merged-code certificate `checkPPM` recomputes.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Certificate skeleton: `PhysMap`, `ChainMapCert`, `ChainMapSquare`, `LogicalInjectionCert`, `HomomorphicCNOTCert`, `SwitchProtocolCert`; structural + recomputed (`verifiedCheck`) checks. |
| [DimensionJump.lean](DimensionJump.lean) | Proof-carrying transversal dimension jump: commuting chain square + transversal, non-degenerate `γ₁` + injective induced map; `checkDimensionJump?` + soundness. |
| [ProductSurgery.lean](ProductSurgery.lean) | Product-surgery / QGPU merged CSS code, recomputed CSS-commutation + merge count; `CapabilityWitness` provenance so `.productSurgery` flows only from a `CheckedProductSurgery`. |
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
    qldpcRegistry.all (fun s => s.status == .lowersToMixIR) = false := by decide
```

## Example

```lean
-- a 2×2 batched switch: k1 = k2 = 2; sources = {⟨0,0⟩,⟨0,1⟩,⟨1,0⟩,⟨1,1⟩}.
def bcs22 : BatchedCodeSwitchSpec :=
  { k1 := 2, k2 := 2, sources := [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], dummies := [] }
example : bcs22.wf = true := by decide
example : ok? (checkBatchedCodeSwitch? bcs22) = true := by decide

-- the carrier lookup changes EXACTLY as (j,i) ↦ (i,j):
example : bcs22.routeMap.loc ⟨0, 1⟩ = ⟨1, 0⟩ := by decide      -- block 0, logical 1 ↦ block 1, logical 0
example : bcs22.routeMap.loc ⟨1, 0⟩ = ⟨0, 1⟩ := by decide      -- block 1, logical 0 ↦ block 0, logical 1
example : bcs22.routeMap.loc ⟨1, 1⟩ = ⟨1, 1⟩ := by decide      -- diagonal fixed
```

A well-formed batched code switch routes the `(block j, logical i)` address to its transpose `(block i, logical j)`, and the route's `LocMap` lookup is checked by `decide`. Source: [BatchedSwitch.lean](BatchedSwitch.lean) (§BCS.4 tests).

## Status & scope

Honest, mirroring the repo's contract tiers (P proved theorem, D `by decide` test, A documented assumption, M missing/planned):

- **Recomputed over GF(2) (P/D).** Chain-square commutation (`∂φ = φ∂`), physical transversality + non-degeneracy of `γ₁`, induced-logical-map injectivity (rank), disjoint-image parallelism, merged-code CSS-commutation, data-stabilizer preservation, merge count `M = rank H_Z'`, batched-route well-formedness/transpose, QGPU basis/alignment/round legality. These carry `by decide` tests and `*_sound` theorems (e.g. `checkDimensionJump?_sound`, `checkProductSurgery?_sound`, `checkQGPURoundIn?_sound`, `checkBatchedCodeSwitchFor?_preservesRoute`). Soundness theorems are the usual `propext`-clean style, NOT "axiom-free".
- **Provenance (P).** `CapabilityWitness` closes the `.productSurgery` bypass: a `.productSurgery` authorization can only come from a `CheckedProductSurgery` (`generic_not_productSurgery`, `genericWitness?`).
- **Deferred / external / assumed (A/M).** Merged-/jumped-code DISTANCE, decoder thresholds, circuit-level fault distance, one-bit-teleportation init/measurement/feedback, the homology-quotient refinement of injectivity, the operational measurement-outcome rule (no `Step` semantics), and ancilla state preparation are all EXPLICIT deferred obligations (recorded as `obligations : List String`). A `GPPMArtifact` is deliberately NOT a `CheckedPrimitive`.
- **MixIR status (P).** Only high-weight capability PPM lowers to MixIR; the other six methods are `externalOnly` (`not_all_lower_to_mixIR`, `only_ppm_lowers`). The `Block`-identity binding for product surgery (`CheckedProductSurgeryFor`) is a recorded BLOCKER, NOT built.
- The `QLDPCPapers/` concrete instances use `native_decide` (out of the M23 axiom-clean scope).

## See also

- [../README.md](../README.md) — the Compiler layer overview.
- [../CONTRACT.md](../CONTRACT.md) — the full correctness-boundary matrix (tier definitions).
- [../../README.md](../../README.md) — repository root.
