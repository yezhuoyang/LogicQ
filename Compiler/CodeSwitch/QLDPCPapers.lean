/-
  Compiler.CodeSwitch.QLDPCPapers -- paper-shaped qLDPC protocol certificates.

  This module packages the qLDPC-operation paper suite as LogicQ language
  constructs over the checked kernels already present in `TypeChecker` and
  `Compiler.CodeSwitch.Basic`.

  Covered protocol shapes:
    * GPPM / fast homological-product logical computation: prepare ancilla,
      apply one-way homomorphic CNOT, measure ancilla, track frame.
    * Transversal dimension jump: sparse chain-map square + injective logical map.
    * Batched high-rate operations / QGPU-style parallelism: many verified jumps
      with pairwise-disjoint image supports and an explicit batch routing matrix.
    * High-rate surgery: a checked PPM capability selected from product/adapter/
      homomorphic measurement families.

  Distance, decoder thresholds, and full stochastic fault-tolerance remain explicit
  obligations.  The checked part here is exactly the GF(2)/symplectic part LogicQ can
  recompute today.
-/
import Compiler.CodeSwitch.Basic
import Compiler.CodeSwitch.ProductSurgery

namespace Compiler.CodeSwitch
open TypeChecker ChainQ.GF2 Logical

/-! ## Literature-level tags. -/

inductive QLDPCPaperTechnique
  | homologicalProductGPPM
  | transversalDimensionJump
  | batchedCodeSwitching
  | batchedAddressableClifford
  | highRateSurgery
  | qgpuParallelLogic
  deriving DecidableEq, Repr

/-! ## Homomorphic CNOT and GPPM. -/

/-- A verified use of a one-way homomorphic CNOT between two code blocks. -/
structure HomomorphicCNOTProtocol where
  control : Nat
  target  : Nat
  cert    : HomomorphicCNOTCert
  srcStab : BoolMat
  tgtStab : BoolMat
  deriving Repr

def HomomorphicCNOTProtocol.verifiedCheck (p : HomomorphicCNOTProtocol) : Bool :=
  p.cert.matchesDirection p.control p.target &&
  p.cert.structuralCheck &&
  p.cert.chain.verifiedCheck p.srcStab p.tgtStab

def HomomorphicCNOTProtocol.verify? (p : HomomorphicCNOTProtocol) :
    Except TypeError HomomorphicCNOTProtocol :=
  if p.verifiedCheck then .ok p
  else .error (.certFailed "homomorphic CNOT protocol failed direction/sparsity/stabilizer checks")

/-- Generalized PPM via homomorphic CNOT into an ancilla code. -/
structure GPPMProtocol where
  dataBlock        : Nat
  ancillaBlock     : Nat
  target           : PPM.MTarget
  homCNOT          : HomomorphicCNOTProtocol
  ancillaPrepared  : Bool
  ancillaMeasured  : Bool
  frameTracked     : Bool
  deriving Repr

def targetOnBlock (P : PPM.MTarget) (b : Nat) : Bool :=
  P.all (fun f => f.1.blk == b)

def GPPMProtocol.verifiedCheck (p : GPPMProtocol) : Bool :=
  p.homCNOT.verifiedCheck &&
  p.homCNOT.control == p.dataBlock &&
  p.homCNOT.target == p.ancillaBlock &&
  ! p.target.isEmpty &&
  p.target.wf &&
  targetOnBlock p.target p.dataBlock &&
  p.ancillaPrepared &&
  p.ancillaMeasured &&
  p.frameTracked

def GPPMProtocol.verify? (p : GPPMProtocol) : Except TypeError GPPMProtocol :=
  if p.verifiedCheck then .ok p
  else .error (.certFailed "GPPM protocol failed homomorphic-CNOT or ancilla/target checks")

/-! ## Dimension jump. -/

/-- A transversal dimension jump: checked chain-map square, checked switch protocol,
    and explicit frame tracking. -/
structure DimensionJumpProtocol where
  switch        : SwitchProtocolCert
  square        : ChainMapSquare
  srcStab       : BoolMat
  tgtStab       : BoolMat
  frameTracked  : Bool
  deriving Repr

/-- The dimension-jump protocol verifies iff: the switch cert verifies, the switch's degree-1
    physical map COINCIDES with the square's `highMap` (`switch.chain.map = square.highMap` — so
    there is a SINGLE coherent degree-1 map, not two independently-checked ones), the chain-map
    square commutes (shape + ∂φ=φ∂), AND — matching the hardened
    `Compiler.CodeSwitch.checkDimensionJump?` — `γ₁ = square.highMap` is physically transversal
    and NON-DEGENERATE (`rank = srcN`, so a zero/collapsing `γ₁` is REJECTED here too), plus the
    frame is tracked.  (The induced logical-map injectivity needs the standalone
    `checkDimensionJump?` which carries the `LogicalInjectionCert`; this protocol shares the
    coherence/non-degeneracy/transversality gates so it can no longer accept an incoherent pair
    or a square the hardened checker rejects.) -/
def DimensionJumpProtocol.verifiedCheck (p : DimensionJumpProtocol) : Bool :=
  p.switch.verifiedCheck p.srcStab p.tgtStab &&
  decide (p.switch.chain.map = p.square.highMap) &&
  p.square.verifiedCheck &&
  p.square.highMap.physicallyTransversal &&
  decide (rank p.square.highMap.matrix = p.square.highMap.srcN) &&
  p.frameTracked

def DimensionJumpProtocol.verify? (p : DimensionJumpProtocol) :
    Except TypeError DimensionJumpProtocol :=
  if p.verifiedCheck then .ok p
  else .error (.certFailed "dimension-jump protocol failed chain/logical/frame checks")

/-! ## Batched high-rate protocols. -/

def pairwiseDisjointSupports : List (List Nat) -> Bool
  | [] => true
  | s :: rest => rest.all (fun t => disjointSupports s t) && pairwiseDisjointSupports rest

structure BatchedJump where
  jump         : DimensionJumpProtocol
  deriving Repr

/-- The image support of a batched jump — COMPUTED from its actual degree-1 map
    (`square.highMap`), never caller-supplied.  Because a verified jump forces
    `switch.chain.map = square.highMap`, this is the genuine physical-qubit image. -/
def BatchedJump.imageSupport (j : BatchedJump) : List Nat :=
  physMapImageRows j.jump.square.highMap

inductive BatchedProtocolKind
  | syndromeExtraction
  | codeSwitching
  | addressableClifford
  | qgpuParallel
  deriving DecidableEq, Repr

structure BatchedProtocol where
  kind              : BatchedProtocolKind
  jumps             : List BatchedJump
  routing           : BoolMat
  syndromeExtractor : Bool
  switchBack        : Bool
  deriving Repr

def BatchedProtocol.verifiedCheck (p : BatchedProtocol) : Bool :=
  ! p.jumps.isEmpty &&
  p.jumps.all (fun j => j.jump.verifiedCheck) &&
  pairwiseDisjointSupports (p.jumps.map (fun j => j.imageSupport)) &&
  decide (p.routing.length = p.jumps.length) &&
  p.routing.all (fun row => decide (row.length = p.jumps.length)) &&
  p.syndromeExtractor &&
  p.switchBack

def BatchedProtocol.verify? (p : BatchedProtocol) : Except TypeError BatchedProtocol :=
  if p.verifiedCheck then .ok p
  else .error (.certFailed "batched qLDPC protocol failed jump/disjoint/routing checks")

/-! ## High-rate surgery. -/

def highRateSurgeryKind : CapKind -> Bool
  | .productSurgery => true
  | .adapterPPM => true
  | .homomorphicMeasurement => true
  | _ => false

/-- High-rate surgery is represented as a verified PPM `CapabilityWitness` (so a
    `.productSurgery` authorization flows ONLY from a `CheckedProductSurgery`, never a raw
    capability) plus explicit ancilla/split/frame obligations. -/
structure HighRateSurgeryProtocol where
  target           : PPM.MTarget
  witness          : CapabilityWitness
  ancillaPrepared  : Bool
  splitMeasured    : Bool
  frameTracked     : Bool

def HighRateSurgeryProtocol.verifiedCheck (Γ : TypedEnv) (p : HighRateSurgeryProtocol) : Bool :=
  highRateSurgeryKind p.witness.toCapability.kind &&
  ok? (checkPPMWitnessed Γ [p.witness] p.target) &&
  p.ancillaPrepared &&
  p.splitMeasured &&
  p.frameTracked

def HighRateSurgeryProtocol.verify? (Γ : TypedEnv) (p : HighRateSurgeryProtocol) :
    Except TypeError HighRateSurgeryProtocol :=
  if p.verifiedCheck Γ then .ok p
  else .error (.certFailed "high-rate surgery protocol failed PPM/witness checks")

/-! ## Soundness extractors. -/

theorem HomomorphicCNOTProtocol.direction_of_verified {p : HomomorphicCNOTProtocol}
    (h : p.verifiedCheck = true) :
    p.cert.matchesDirection p.control p.target = true := by
  simp only [HomomorphicCNOTProtocol.verifiedCheck, Bool.and_eq_true] at h
  exact h.1.1

theorem GPPMProtocol.homCNOT_of_verified {p : GPPMProtocol}
    (h : p.verifiedCheck = true) :
    p.homCNOT.verifiedCheck = true := by
  simp only [GPPMProtocol.verifiedCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1

theorem DimensionJumpProtocol.switch_of_verified {p : DimensionJumpProtocol}
    (h : p.verifiedCheck = true) :
    p.switch.verifiedCheck p.srcStab p.tgtStab = true := by
  simp only [DimensionJumpProtocol.verifiedCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1

/-- **Map coherence (load-bearing).**  A verified dimension jump has a SINGLE degree-1 physical
    map: the switch cert's `chain.map` IS the square's `highMap`.  So an adversary cannot pass an
    identity `switch.chain.map` next to a swap `square.highMap` — the two are forced equal. -/
theorem DimensionJumpProtocol.map_coherent_of_verified {p : DimensionJumpProtocol}
    (h : p.verifiedCheck = true) :
    p.switch.chain.map = p.square.highMap := by
  simp only [DimensionJumpProtocol.verifiedCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2

/-! ## Tiny executable witnesses. -/

def toyHomCNOT : HomomorphicCNOTProtocol :=
  { control := 0, target := 1, cert := cnot01,
    srcStab := [[true, false]], tgtStab := [[true, false]] }

example : toyHomCNOT.verifiedCheck = true := by decide
example : ok? toyHomCNOT.verify? = true := by decide

def toyGPPM : GPPMProtocol :=
  { dataBlock := 0, ancillaBlock := 1,
    target := [(⟨0, 0⟩, PPM.PLetter.Z)],
    homCNOT := toyHomCNOT,
    ancillaPrepared := true, ancillaMeasured := true, frameTracked := true }

example : toyGPPM.verifiedCheck = true := by decide
example : targetOnBlock toyGPPM.target 0 = true := by decide

def toyJump : DimensionJumpProtocol :=
  { switch := goodSwitch, square := goodSquare,
    srcStab := [[true, false]], tgtStab := [[true, false]], frameTracked := true }

example : toyJump.verifiedCheck = true := by decide
example : ok? toyJump.verify? = true := by decide
-- Concern 2: a DEGENERATE (rank-deficient) γ₁ square is now REJECTED by
-- `DimensionJumpProtocol.verify?` (matching the hardened `checkDimensionJump?`), not silently
-- accepted via shape+commute.  Here γ₁ = `[[1,0],[0,0]]` is TRANSVERSAL and COMMUTES (highMap =
-- lowMap, identity boundaries) but has rank 1 ≠ srcN 2 — the non-degeneracy gate catches it.
def toyJumpDegenerate : DimensionJumpProtocol :=
  { toyJump with square := { goodSquare with
      highMap := { srcN := 2, tgtN := 2, matrix := [[true, false], [false, false]] },
      lowMap  := { srcN := 2, tgtN := 2, matrix := [[true, false], [false, false]] } } }
example : toyJumpDegenerate.square.verifiedCheck = true := by decide   -- shape + commute still pass…
example : ok? toyJumpDegenerate.verify? = false := by decide           -- …but verify? now REJECTS it

-- Concern 1 (map coherence): an INCOHERENT protocol — `switch.chain.map` = identity (goodSwitch)
-- but `square.highMap` = SWAP — is now REJECTED.  The square itself is fully valid (commutes +
-- transversal + non-degenerate), so ONLY the coherence guard `switch.chain.map = square.highMap`
-- fires: an adversary can no longer pin two different degree-1 maps next to each other.
def jumpSwapMap : PhysMap := { srcN := 2, tgtN := 2, matrix := [[false, true], [true, false]] }
def toyJumpMismatch : DimensionJumpProtocol :=
  { toyJump with square := { goodSquare with highMap := jumpSwapMap, lowMap := jumpSwapMap } }
example : toyJumpMismatch.square.verifiedCheck = true := by decide                            -- the square is valid…
example : decide (toyJumpMismatch.switch.chain.map = toyJumpMismatch.square.highMap) = false := by decide  -- …but incoherent…
example : ok? toyJumpMismatch.verify? = false := by decide                                    -- …so verify? REJECTS it

def toyBatch : BatchedProtocol :=
  { kind := .addressableClifford,
    jumps := [{ jump := toyJump }],
    routing := [[true]],
    syndromeExtractor := true,
    switchBack := true }

example : toyBatch.verifiedCheck = true := by decide
example : pairwiseDisjointSupports [[0, 1], [2, 3]] = true := by decide
example : pairwiseDisjointSupports [[0, 1], [1, 3]] = false := by decide

-- Concern 2 (batched): supports are COMPUTED from the actual `γ₁` maps — a caller can no longer
-- fake disjointness.  TWO identical jumps share the SAME computed image, so the batch is
-- REJECTED (no fake `imageSupport := [0]` / `[1]` can rescue it):
def toyBatchClash : BatchedProtocol :=
  { toyBatch with jumps := [{ jump := toyJump }, { jump := toyJump }], routing := [[true, false], [false, true]] }
example : ({ jump := toyJump } : BatchedJump).imageSupport = [0, 1] := by decide   -- computed, not supplied
example : pairwiseDisjointSupports ([toyJump.square.highMap, toyJump.square.highMap].map physMapImageRows) = false := by decide
example : ok? toyBatchClash.verify? = false := by decide
-- …and TRULY disjoint maps (images [0] vs [1]) are ACCEPTED:
def jumpImg0Map : PhysMap := { srcN := 1, tgtN := 2, matrix := [[true], [false]] }
def jumpImg1Map : PhysMap := { srcN := 1, tgtN := 2, matrix := [[false], [true]] }

def jumpImg0Chain : ChainMapCert :=
  { map := jumpImg0Map,
    claimedChainCommutes := goodChain.claimedChainCommutes,
    claimedStabilizerPreserved := goodChain.claimedStabilizerPreserved }
def jumpImg1Chain : ChainMapCert :=
  { map := jumpImg1Map,
    claimedChainCommutes := goodChain.claimedChainCommutes,
    claimedStabilizerPreserved := goodChain.claimedStabilizerPreserved }

def jumpImg0Switch : SwitchProtocolCert :=
  { srcBlock := goodSwitch.srcBlock,
    tgtBlock := goodSwitch.tgtBlock,
    chain := jumpImg0Chain,
    injection := goodSwitch.injection,
    disjointFromOthers := goodSwitch.disjointFromOthers,
    deferred := goodSwitch.deferred,
    distance := goodSwitch.distance }
def jumpImg1Switch : SwitchProtocolCert :=
  { srcBlock := goodSwitch.srcBlock,
    tgtBlock := goodSwitch.tgtBlock,
    chain := jumpImg1Chain,
    injection := goodSwitch.injection,
    disjointFromOthers := goodSwitch.disjointFromOthers,
    deferred := goodSwitch.deferred,
    distance := goodSwitch.distance }

def jumpImg0Square : ChainMapSquare :=
  { srcBoundary := goodSquare.srcBoundary,
    tgtBoundary := goodSquare.tgtBoundary,
    highMap := jumpImg0Map,
    lowMap := jumpImg0Map }
def jumpImg1Square : ChainMapSquare :=
  { srcBoundary := goodSquare.srcBoundary,
    tgtBoundary := goodSquare.tgtBoundary,
    highMap := jumpImg1Map,
    lowMap := jumpImg1Map }

def jumpImg0 : DimensionJumpProtocol :=
  { switch := jumpImg0Switch,
    square := jumpImg0Square,
    srcStab := toyJump.srcStab,
    tgtStab := toyJump.tgtStab,
    frameTracked := toyJump.frameTracked }
def jumpImg1 : DimensionJumpProtocol :=
  { switch := jumpImg1Switch,
    square := jumpImg1Square,
    srcStab := toyJump.srcStab,
    tgtStab := toyJump.tgtStab,
    frameTracked := toyJump.frameTracked }
example : ({ jump := jumpImg0 } : BatchedJump).imageSupport = [0] := by decide
example : ({ jump := jumpImg1 } : BatchedJump).imageSupport = [1] := by decide
example : pairwiseDisjointSupports ([jumpImg0.square.highMap, jumpImg1.square.highMap].map physMapImageRows) = true := by decide

def toyBareBlock : Block :=
  { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }

def toySurgeryEnv : TypedEnv := ⟨[⟨toyBareBlock, by decide⟩, ⟨toyBareBlock, by decide⟩]⟩

-- a GENERIC (adapter) cross-block merged capability — NOT falsely `.productSurgery`:
def toyHighRateCap : Capability :=
  { kind := .adapterPPM, blocks := [0, 1], ancN := 0,
    connStab := [[false, false, true, true]] }

def toyHighRateSurgery : HighRateSurgeryProtocol :=
  { target := [(⟨0, 0⟩, PPM.PLetter.Z), (⟨1, 0⟩, PPM.PLetter.Z)],
    witness := .generic toyHighRateCap (by decide),
    ancillaPrepared := true,
    splitMeasured := true,
    frameTracked := true }

example : toyHighRateSurgery.verifiedCheck toySurgeryEnv = true := by decide
example : ok? (toyHighRateSurgery.verify? toySurgeryEnv) = true := by decide

-- THE CLOSED BYPASS: a RAW `.productSurgery` capability cannot enter the paper API — it is
-- rejected by `genericWitness?`, and `.generic` cannot wrap it (provenance flows only through
-- `CapabilityWitness.productSurgery` from a `CheckedProductSurgery`):
def toyRawProductSurgeryCap : Capability := { toyHighRateCap with kind := .productSurgery }
example : ok? (genericWitness? toyRawProductSurgeryCap) = false := by decide
example : ok? (genericWitness? toyHighRateCap) = true := by decide

end Compiler.CodeSwitch
