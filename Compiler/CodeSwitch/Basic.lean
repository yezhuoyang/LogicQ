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
  deriving Repr

/-- The map has the declared shape (`tgtN` rows, each of width `srcN`). -/
def PhysMap.shapeWf (φ : PhysMap) : Bool :=
  decide (φ.matrix.length = φ.tgtN) && φ.matrix.all (fun r => decide (r.length = φ.srcN))

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

/-! ## §6. Deferred fault obligations + the top-level switch protocol cert. -/

/-- Fault obligations a switch DEFERS (uncertified here). -/
structure SwitchFaultObligations where
  distancePreserved : Bool := false   -- merged/jumped-code distance ≥ d (DEFERRED)
  faultDistance     : Bool := false   -- circuit-level fault distance (DEFERRED)
  decoderThreshold  : Bool := false   -- decoder threshold (DEFERRED)
  deriving Repr, DecidableEq

/-- The top-level CODE-SWITCH / dimension-jump protocol certificate: source/target
    blocks, the chain map, the induced logical injection, the disjoint-image flag
    (for batched parallel jumps), and the DEFERRED fault obligations. -/
structure SwitchProtocolCert where
  srcBlock        : Nat
  tgtBlock        : Nat
  chain           : ChainMapCert
  injection       : LogicalInjectionCert
  disjointFromOthers : Bool                  -- safe to run in parallel with its batch
  deferred        : SwitchFaultObligations
  deriving Repr

/-- The COMPUTABLE checks: well-shaped chain map, injective induced logical map, and
    the fault obligations HONESTLY deferred (all `false`).  Does NOT certify
    distance / fault-distance / full switch correctness. -/
def SwitchProtocolCert.structuralCheck (c : SwitchProtocolCert) : Bool :=
  c.chain.structuralCheck && c.injection.structuralCheck
  && ! c.deferred.distancePreserved && ! c.deferred.faultDistance && ! c.deferred.decoderThreshold

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

-- NON-INJECTIVE induced logical map is rejected (not logically transversal):
example : LogicalInjectionCert.structuralCheck { inducedLogicalMap := [[true]], claimedInjective := false } = false := by decide
example : goodInjection.structuralCheck = true := by decide

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
-- INVALID switch syntax #1: a shape-mismatched chain map FAILS the structural check.
def badShapeSwitch : SwitchProtocolCert :=
  { goodSwitch with chain :=
      { map := { srcN := 2, tgtN := 2, matrix := [[true]] },   -- 1×1, not 2×2
        claimedChainCommutes := true, claimedStabilizerPreserved := true } }
example : badShapeSwitch.structuralCheck = false := by decide
-- INVALID switch syntax #2: a non-injective induced logical map FAILS (not logically transversal).
example : SwitchProtocolCert.structuralCheck
    { goodSwitch with injection := { inducedLogicalMap := [[true]], claimedInjective := false } } = false := by decide
-- INVALID switch syntax #3: dishonestly marking the distance CERTIFIED FAILS the check.
example : SwitchProtocolCert.structuralCheck { goodSwitch with deferred := { distancePreserved := true } } = false := by decide

end Compiler.CodeSwitch
