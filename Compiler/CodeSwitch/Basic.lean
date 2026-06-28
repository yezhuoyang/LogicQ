/-
  Compiler.CodeSwitch — the TYPED CERTIFICATE SKELETON for code switching /
  dimension jump / homomorphic CNOT (M14 task 5).

  EXTERNAL / ASSUMED CERTIFICATES — NOT VERIFICATION (M15 task 5).  These certs fix
  the SHAPE of the data a code switch must carry; they do NOT prove the switch is
  correct or fault-tolerant.  The `claimed…` fields are recorded CLAIMS supplied by
  an external construction (NOT decided over GF(2) here).  `structuralCheck` only
  checks SHAPE / DIRECTION / the injectivity-CLAIM flag — never the chain-map
  commutation, stabilizer preservation, distance, or fault-distance, which are
  EXTERNAL/DEFERRED.  This is a SEPARATE typed layer above the M7 symplectic
  `SwitchCert`; wiring the two together is left to a later pass.

  Grounding (Library/sources):
    * chain maps / homomorphic CNOTs / induced logical maps / injectivity (logical
      transversality) / disjoint-image parallelism — 2510.07269 (Transversal
      dimension jump for product qLDPC codes: chain map `φ`, the induced `γ̄₁` and
      its injectivity, disjoint-image condition for parallel jumps).
    * adapters as explicit merge objects with PORTS + graph witnesses + preserved
      logical action — 2410.03628 (Universal adapters).
    * code-switching gadgets = state prep + homomorphic CNOT + transversal
      measurement + classical postprocessing; resources/fault assumptions explicit
      — 2510.08552 (Single-shot universality via code-switching).
-/
import TypeChecker.Basic
import Physical.Basic

namespace Compiler.CodeSwitch
open TypeChecker ChainQ.GF2 Logical

/-! ## §1. A physical (chain-level) map between two codes. -/

/-- A physical linear map `φ : C_src → C_tgt` at one chain degree, as a `tgtN × srcN`
    `BoolMat` over GF(2).  `shapeWf` is the only structurally-checkable shape fact. -/
structure PhysMap where
  srcN   : Nat
  tgtN   : Nat
  matrix : BoolMat
  deriving Repr, DecidableEq

/-- The map has the declared shape (`tgtN` rows, each of width `srcN`). -/
def PhysMap.shapeWf (φ : PhysMap) : Bool :=
  decide (φ.matrix.length = φ.tgtN) && φ.matrix.all (fun r => decide (r.length = φ.srcN))

/-- Reinterpret the column-style physical map as a row-vector action on Pauli/check rows. -/
def PhysMap.applyRows (φ : PhysMap) (rows : BoolMat) : BoolMat :=
  matMul rows (transpose φ.matrix φ.srcN) φ.tgtN

/-- Physical transversality/sparsity: every source and target coordinate is used at
    most once. -/
def PhysMap.physicallyTransversal (φ : PhysMap) : Bool :=
  φ.shapeWf &&
  φ.matrix.all TypeChecker.Internal.atMostOneTrue &&
  (transpose φ.matrix φ.srcN).all TypeChecker.Internal.atMostOneTrue

/-! ## §2. Chain-map / stabilizer-preservation certificate. -/

/-- A CHAIN-MAP certificate: the physical map commutes with the boundary maps
    (`∂_tgt ∘ φ = φ ∘ ∂_src`) and carries stabilizers into stabilizers.  The
    chain-commutation and stabilizer-preservation are recorded as CLAIMS here
    (`claimed…`) — the full GF(2) commutation check is the next layer. -/
structure ChainMapCert where
  map                      : PhysMap
  claimedChainCommutes     : Bool   -- (2510.07269) ∂φ = φ∂
  claimedStabilizerPreserved : Bool -- maps stabilizer rows into the target stabilizer span
  deriving Repr

/-- The COMPUTABLE part of a chain-map cert: the physical map is well-shaped. -/
def ChainMapCert.structuralCheck (c : ChainMapCert) : Bool := c.map.shapeWf

/-- Recompute stabilizer preservation instead of trusting the recorded claim. -/
def ChainMapCert.stabilizerPreserved (c : ChainMapCert) (srcStab tgtStab : BoolMat) : Bool :=
  (c.map.applyRows srcStab).all (fun r => inSpan tgtStab r)

/-- The currently checkable part of a chain-map certificate. -/
def ChainMapCert.verifiedCheck (c : ChainMapCert) (srcStab tgtStab : BoolMat) : Bool :=
  c.map.physicallyTransversal && c.stabilizerPreserved srcStab tgtStab

/-! ## §2b. One computable chain-map square. -/

/-- A single chain-map square in row-vector convention. -/
structure ChainMapSquare where
  srcBoundary : BoolMat
  tgtBoundary : BoolMat
  highMap     : PhysMap
  lowMap      : PhysMap
  deriving Repr

def ChainMapSquare.shapeWf (s : ChainMapSquare) : Bool :=
  s.highMap.shapeWf && s.lowMap.shapeWf &&
  decide (s.srcBoundary.length = s.highMap.srcN) &&
  s.srcBoundary.all (fun r => decide (r.length = s.lowMap.srcN)) &&
  decide (s.tgtBoundary.length = s.highMap.tgtN) &&
  s.tgtBoundary.all (fun r => decide (r.length = s.lowMap.tgtN))

/-- Check `tgtBoundary ∘ highMap = lowMap ∘ srcBoundary`. -/
def ChainMapSquare.commutes (s : ChainMapSquare) : Bool :=
  let highRows := s.highMap.applyRows (TypeChecker.idMat s.highMap.srcN)
  let viaTarget := matMul highRows s.tgtBoundary s.lowMap.tgtN
  let viaSource := s.lowMap.applyRows s.srcBoundary
  decide (viaTarget = viaSource)

def ChainMapSquare.verifiedCheck (s : ChainMapSquare) : Bool :=
  s.shapeWf && s.commutes

/-! ## §3. Induced logical map + injectivity (logical transversality). -/

/-- The induced map `γ̄` on LOGICAL operators, with its injectivity flag.  Injective
    `γ̄` ⇔ no logical is collapsed ⇔ the switch is LOGICALLY TRANSVERSAL
    (2510.07269: injectivity of `γ̄₁`). -/
structure LogicalInjectionCert where
  inducedLogicalMap : BoolMat
  claimedInjective  : Bool
  deriving Repr

/-- A logical map is acceptable only if it is (claimed) injective: a non-injective
    induced map is NOT logically transversal. -/
def LogicalInjectionCert.structuralCheck (c : LogicalInjectionCert) : Bool := c.claimedInjective

/-- Recompute injectivity of the represented logical map by row rank. -/
def LogicalInjectionCert.computableInjective (c : LogicalInjectionCert) : Bool :=
  rank c.inducedLogicalMap == c.inducedLogicalMap.length

/-- The injection is verified iff the recomputed rank-injectivity holds AND the recorded
    `claimedInjective` flag AGREES with it (so the flag is load-bearing, never ignored). -/
def LogicalInjectionCert.verifiedCheck (c : LogicalInjectionCert) : Bool :=
  c.claimedInjective && c.computableInjective

/-! ## §4. Homomorphic CNOT (one-way) certificate. -/

/-- A HOMOMORPHIC-CNOT certificate `control ▸ target`.  Directionality is
    LOAD-BEARING: a CNOT is NOT symmetric, so the cert names a specific
    `control`/`target` and matches only that direction. -/
structure HomomorphicCNOTCert where
  control        : Nat
  target         : Nat
  chain          : ChainMapCert
  byproductFrame : List (LQubit × Physical.Pauli)   -- (track-not-apply) frame rule
  deriving Repr

/-- Does this cert certify the CNOT in direction `c ▸ t`?  Reversing the direction
    (`t ▸ c`) does NOT match — one-way. -/
def HomomorphicCNOTCert.matchesDirection (cert : HomomorphicCNOTCert) (c t : Nat) : Bool :=
  cert.control == c && cert.target == t

/-- A homomorphic-CNOT cert is well-formed: distinct control/target (no self-CNOT)
    and a well-shaped chain map. -/
def HomomorphicCNOTCert.structuralCheck (cert : HomomorphicCNOTCert) : Bool :=
  ! (cert.control == cert.target) && cert.chain.structuralCheck

/-! ## §5. Disjoint-image condition for PARALLEL switches. -/

/-- Two image supports are DISJOINT (the precondition for running two switches /
    homomorphic CNOTs in parallel — 2510.07269 disjoint-image condition). -/
def disjointSupports (a b : List Nat) : Bool := a.all (fun x => ! b.contains x)

/-- The image (nonzero-row indices) of a `γ` map — its physical-qubit support.  Defined here
    (upstream of both `DimensionJump` and `QLDPCPapers`) so disjointness is COMPUTED from the
    actual map, never caller-supplied. -/
def physMapImageRows (φ : PhysMap) : List Nat :=
  (List.range φ.matrix.length).filter (fun i => (φ.matrix.getD i []).any (fun b => b))

/-! ## §6. Deferred fault obligations + the top-level switch protocol cert. -/

/-- Fault obligations a switch DEFERS (uncertified here). -/
structure SwitchFaultObligations where
  distancePreserved : Bool := false   -- merged/jumped-code distance ≥ d (DEFERRED)
  faultDistance     : Bool := false   -- circuit-level fault distance (DEFERRED)
  decoderThreshold  : Bool := false   -- decoder threshold (DEFERRED)
  deriving Repr, DecidableEq

/-- The top-level CODE-SWITCH / dimension-jump protocol certificate: source/target
    blocks, the chain map, the induced logical injection, the disjoint-image flag
    (for batched parallel jumps), deferred fault obligations, and an optional
    checked distance lower-bound obligation. -/
structure SwitchProtocolCert where
  srcBlock        : Nat
  tgtBlock        : Nat
  chain           : ChainMapCert
  injection       : LogicalInjectionCert
  disjointFromOthers : Bool                  -- safe to run in parallel with its batch
  deferred        : SwitchFaultObligations
  distance        : Option DistanceObligation := none
  deriving Repr

/-- Distance is either honestly deferred (`distancePreserved = false`) or backed
    by a verified lower-bound obligation. -/
def SwitchProtocolCert.distanceCheck (c : SwitchProtocolCert) : Bool :=
  match c.distance with
  | some obligation => obligation.verifiedCheck
  | none => ! c.deferred.distancePreserved

/-- The COMPUTABLE checks: well-shaped chain map, injective induced logical map,
    distance either honestly deferred or checked, and the remaining fault
    obligations honestly deferred.  Does NOT certify circuit fault-distance,
    decoder threshold, or full stochastic switch correctness. -/
def SwitchProtocolCert.structuralCheck (c : SwitchProtocolCert) : Bool :=
  c.chain.structuralCheck && c.injection.structuralCheck
  && c.distanceCheck && ! c.deferred.faultDistance && ! c.deferred.decoderThreshold

/-- Recompute the GF(2)-checkable part of a code-switch protocol.  Distance can
    be discharged by a `DistanceObligation`; decoder/fault-distance conditions
    still stay deferred here. -/
def SwitchProtocolCert.verifiedCheck (c : SwitchProtocolCert) (srcStab tgtStab : BoolMat) : Bool :=
  c.chain.verifiedCheck srcStab tgtStab &&
  c.injection.verifiedCheck &&
  c.disjointFromOthers &&
  c.distanceCheck && ! c.deferred.faultDistance && ! c.deferred.decoderThreshold

def SwitchProtocolCert.verify? (c : SwitchProtocolCert) (srcStab tgtStab : BoolMat) :
    Except TypeError SwitchProtocolCert :=
  if c.verifiedCheck srcStab tgtStab then .ok c
  else .error (.certFailed "code-switch protocol failed recomputed GF(2) checks")

/-! ## §7. Tiny tests. -/

/-- A well-shaped 2→2 chain map (identity-ish), injective logical map. -/
def goodChain : ChainMapCert :=
  { map := { srcN := 2, tgtN := 2, matrix := [[true, false], [false, true]] },
    claimedChainCommutes := true, claimedStabilizerPreserved := true }
def goodInjection : LogicalInjectionCert :=
  { inducedLogicalMap := [[true, false], [false, true]], claimedInjective := true }

-- BAD SHAPE is rejected: a 2→2 cert whose matrix is 1×3 fails `check`.
example : ChainMapCert.structuralCheck
    { map := { srcN := 2, tgtN := 2, matrix := [[true, false, false]] },
      claimedChainCommutes := true, claimedStabilizerPreserved := true } = false := by decide
example : goodChain.structuralCheck = true := by decide
example : goodChain.map.physicallyTransversal = true := by decide
example : goodChain.verifiedCheck [[true, false]] [[true, false]] = true := by decide
example : goodChain.verifiedCheck [[true, false]] [[false, true]] = false := by decide

def goodSquare : ChainMapSquare :=
  { srcBoundary := [[true, false], [false, true]],
    tgtBoundary := [[true, false], [false, true]],
    highMap := goodChain.map,
    lowMap := goodChain.map }

example : goodSquare.verifiedCheck = true := by decide
example : { goodSquare with tgtBoundary := [[false, true], [true, false]] }.verifiedCheck = false := by decide

-- NON-INJECTIVE induced logical map is rejected (not logically transversal):
example : LogicalInjectionCert.structuralCheck { inducedLogicalMap := [[true]], claimedInjective := false } = false := by decide
example : goodInjection.structuralCheck = true := by decide
example : goodInjection.verifiedCheck = true := by decide
example : LogicalInjectionCert.verifiedCheck
    { inducedLogicalMap := [[true, false], [true, false]], claimedInjective := true } = false := by decide

-- DIRECTION matters: a `0 ▸ 1` homomorphic CNOT matches `0 ▸ 1` but NOT the reversal `1 ▸ 0`:
def cnot01 : HomomorphicCNOTCert :=
  { control := 0, target := 1, chain := goodChain, byproductFrame := [] }
example : cnot01.matchesDirection 0 1 = true := by decide
example : cnot01.matchesDirection 1 0 = false := by decide   -- one-way: reversal rejected
example : cnot01.structuralCheck = true := by decide
-- a self-CNOT (control = target) is rejected:
example : HomomorphicCNOTCert.structuralCheck { control := 0, target := 0, chain := goodChain, byproductFrame := [] } = false := by decide

-- DISJOINT-IMAGE checker distinguishes disjoint from overlapping supports:
example : disjointSupports [0, 1] [2, 3] = true := by decide
example : disjointSupports [0, 1] [1, 2] = false := by decide

-- The protocol cert: computable checks pass; fault obligations stay deferred (false).
def goodSwitch : SwitchProtocolCert :=
  { srcBlock := 0, tgtBlock := 1, chain := goodChain, injection := goodInjection,
    disjointFromOthers := true, deferred := {} }
-- VALID switch syntax: well-shaped chain, injective induced map, all faults deferred.
example : goodSwitch.structuralCheck = true := by decide
example : goodSwitch.deferred.faultDistance = false := by decide
example : goodSwitch.verifiedCheck [[true, false]] [[true, false]] = true := by decide
example : ok? (goodSwitch.verify? [[true, false]] [[true, false]]) = true := by decide
-- INVALID switch syntax #1: a shape-mismatched chain map FAILS the structural check.
def badShapeSwitch : SwitchProtocolCert :=
  { goodSwitch with chain :=
      { map := { srcN := 2, tgtN := 2, matrix := [[true]] },   -- 1×1, not 2×2
        claimedChainCommutes := true, claimedStabilizerPreserved := true } }
example : badShapeSwitch.structuralCheck = false := by decide
-- INVALID switch syntax #2: a non-injective induced logical map FAILS (not logically transversal).
example : SwitchProtocolCert.structuralCheck
    { goodSwitch with injection := { inducedLogicalMap := [[true]], claimedInjective := false } } = false := by decide
example : SwitchProtocolCert.verifiedCheck
    { goodSwitch with injection := { inducedLogicalMap := [[true], [true]], claimedInjective := true } }
    [[true, false]] [[true, false]] = false := by decide
-- Concern 3: `claimedInjective` is LOAD-BEARING in the VERIFIED path.  The matrix below is
-- rank-injective (`computableInjective = true`), so the ONLY thing distinguishing accept from
-- reject is the flag — `verifiedCheck = claimedInjective && computableInjective` rejects when
-- the flag dishonestly disagrees with the recomputed rank:
example : LogicalInjectionCert.computableInjective
    { inducedLogicalMap := [[true, false], [false, true]], claimedInjective := false } = true := by decide
example : LogicalInjectionCert.verifiedCheck
    { inducedLogicalMap := [[true, false], [false, true]], claimedInjective := false } = false := by decide
example : LogicalInjectionCert.verifiedCheck
    { inducedLogicalMap := [[true, false], [false, true]], claimedInjective := true } = true := by decide
-- …and `SwitchProtocolCert.verifiedCheck` inherits it (delegates to `injection.verifiedCheck`):
example : SwitchProtocolCert.verifiedCheck
    { goodSwitch with injection := { inducedLogicalMap := [[true, false], [false, true]], claimedInjective := false } }
    [[true, false]] [[true, false]] = false := by decide
-- INVALID switch syntax #3: dishonestly marking the distance CERTIFIED FAILS the check.
example : SwitchProtocolCert.structuralCheck { goodSwitch with deferred := { distancePreserved := true } } = false := by decide
def goodDistanceObligation : DistanceObligation :=
  { required := 1,
    reason := "toy checked lower bound",
    bounds := ChainQ.paperTableExact "toy exact distance theorem" 1 }
def goodSwitchWithDistance : SwitchProtocolCert :=
  { goodSwitch with deferred := { distancePreserved := true }, distance := some goodDistanceObligation }
example : goodSwitchWithDistance.structuralCheck = true := by decide
example : goodSwitchWithDistance.verifiedCheck [[true, false]] [[true, false]] = true := by decide
def badDistanceObligation : DistanceObligation :=
  { goodDistanceObligation with required := 2 }
def badSwitchWithDistance : SwitchProtocolCert :=
  { goodSwitch with deferred := { distancePreserved := true }, distance := some badDistanceObligation }
example : badSwitchWithDistance.structuralCheck = false := by decide
example : SwitchProtocolCert.verifiedCheck { goodSwitch with disjointFromOthers := false }
    [[true, false]] [[true, false]] = false := by decide

end Compiler.CodeSwitch
