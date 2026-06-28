/-
  Compiler.CodeSwitch.DimensionJump — a TYPED dimension-jump certificate (2510.07269,
  2407.18490).

  A genuine dimension jump is NOT a same-arity code switch: it is a chain map
  `γ = {γ_i}` between the SOURCE and TARGET chain complexes (a 2D↔3D product-qLDPC jump)
  with explicit boundary maps, whose:

    * chain-square COMMUTES — `∂^B_i γ_i = γ_{i-1} ∂^A_i` (recomputed by
      `ChainMapSquare.commutes` over GF(2));
    * degree-1 map `γ_1` has a PHYSICALLY-TRANSVERSAL binary lift (row/column weight ≤ 1,
      recomputed by `PhysMap.physicallyTransversal`);
    * induced logical map `γ̄_1` is INJECTIVE (logical transversality — `ker γ̄_1 = 0`,
      recomputed by `LogicalInjectionCert.computableInjective` = `rank == length`);
    * parallel copies have DISJOINT IMAGES (recomputed by `pairwiseDisjointSupports`).

  This is a REAL recomputed certificate distinct from `checkSwitch` (same-arity).  HONEST
  SCOPE: the one-bit-teleportation init / measurement / feedback, the merged/jumped-code
  DISTANCE, and the homology-QUOTIENT refinement of injectivity (reduce `γ̄_1` modulo the
  target `im ∂_2` — `computableInjective` here is rank-injectivity of the induced map) are
  EXPLICIT deferred obligations.  Same-arity `checkSwitch` remains separate.
-/
import Compiler.CodeSwitch.QLDPCPapers

namespace Compiler.CodeSwitch
open ChainQ.GF2 TypeChecker

/-! ## §DJ.1. The dimension-jump certificate. -/

/-- The induced logical map `γ̄₁` is DIMENSION-COMPATIBLE with `γ₁ = highMap`: it is nonempty
    and maps at most `srcN` source logicals to at most `tgtN` target logicals (a logical map
    of a `tgtN × srcN` physical chain map cannot exceed those bounds).  This REJECTS an
    arbitrary injective matrix of unrelated size paired with the square. -/
def inducedDimCompat (γ1 : PhysMap) (induced : LogicalInjectionCert) : Bool :=
  ! induced.inducedLogicalMap.isEmpty &&
  decide (induced.inducedLogicalMap.length ≤ γ1.srcN) &&
  induced.inducedLogicalMap.all (fun r => decide (r.length ≤ γ1.tgtN))

/-- A proof-carrying dimension-jump certificate.  The degree-1 map `γ_1` is the chain
    square's `highMap` (NOT an independent argument), so injectivity/transversality are
    about the SAME map that the commuting square certifies.  RECOMPUTED: the square commutes
    (`∂φ = φ∂`), `γ_1 = square.highMap` is physically transversal AND NON-DEGENERATE (full
    column rank — rejects the zero/collapsing map), the induced logical map is injective, AND
    it is dimension-compatible with `γ_1`.  The one-bit-teleport / distance / homology-quotient
    facts are the explicit deferred `obligations` (the induced map is an EXTERNAL
    induced-homology witness — its dims are checked, the homology-quotient is deferred). -/
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

/-- The degree-1 chain map `γ_1` of a dimension jump is the square's `highMap`. -/
abbrev DimensionJumpChecked.gamma1 (r : DimensionJumpChecked) : PhysMap := r.square.highMap

/-- The deferred obligations of a dimension jump (NOT recomputable here). -/
def dimensionJumpObligations : List String :=
  ["one-bit teleportation: ancilla init in the required basis (DEFERRED)",
   "one-bit teleportation: measurement basis + outcome (DEFERRED)",
   "byproduct frame / feedback (typed by Compiler.ChainQ2Mixed.Frame; operational rule DEFERRED)",
   "jumped-code distance d̃ ≥ d (DEFERRED)",
   "induced logical map γ̄₁ tied to γ₁ only via dims + injectivity; full homology-quotient (mod target im ∂₂) is a DEFERRED external induced-homology witness"]

/-- **Check a dimension jump.**  Recomputes the chain-square commutation `∂φ = φ∂`, the
    binary-lift transversality + NON-DEGENERACY of `γ_1 = square.highMap` (rejects a zero /
    collapsing map), and the injectivity of the induced logical map.  Returns proof-carrying
    evidence or rejects. -/
def checkDimensionJump? (square : ChainMapSquare) (induced : LogicalInjectionCert) :
    Except TypeError DimensionJumpChecked :=
  if hc : square.verifiedCheck = true then
    if ht : square.highMap.physicallyTransversal = true then
      if hn : decide (rank square.highMap.matrix = square.highMap.srcN) = true then
        if hi : induced.computableInjective = true then
          if hj : induced.claimedInjective = true then
            if hd : inducedDimCompat square.highMap induced = true then
              .ok { square := square, induced := induced, squareComm := hc, transversal := ht,
                    nondegenerate := hn, injective := hi, claimedOk := hj, dimCompat := hd, obligations := dimensionJumpObligations }
            else .error (.certFailed "dimension jump: induced logical map γ̄₁ has dimensions unrelated to γ₁ = square.highMap")
          else .error (.certFailed "dimension jump: induced cert's claimedInjective flag is false (must agree with the computed rank)")
        else .error (.certFailed "dimension jump: induced logical map γ̄₁ is not injective (not logically transversal)")
      else .error (.certFailed "dimension jump: γ₁ = square.highMap is DEGENERATE (zero / not full column rank)")
    else .error (.certFailed "dimension jump: γ₁ = square.highMap is not physically transversal (row/column weight > 1)")
  else .error (.certFailed "dimension jump: chain-map square does not commute (∂φ ≠ φ∂)")

/-- **Dimension-jump soundness.**  A successfully checked jump RECOMPUTED: the chain-square
    commutes, `γ_1 = square.highMap` is physically transversal AND non-degenerate, and the
    induced logical map is injective.  (NOT distance / FT / teleportation correctness — those
    are the deferred `obligations`.) -/
theorem checkDimensionJump?_sound {square : ChainMapSquare}
    {induced : LogicalInjectionCert} {r : DimensionJumpChecked}
    (_h : checkDimensionJump? square induced = .ok r) :
    r.square.verifiedCheck = true ∧ r.square.highMap.physicallyTransversal = true ∧
      decide (rank r.square.highMap.matrix = r.square.highMap.srcN) = true ∧
      r.induced.computableInjective = true ∧ r.induced.claimedInjective = true ∧
      inducedDimCompat r.square.highMap r.induced = true :=
  ⟨r.squareComm, r.transversal, r.nondegenerate, r.injective, r.claimedOk, r.dimCompat⟩

/-- **Parallel dimension jumps** (the multi-copy corollary): the per-copy image supports —
    COMPUTED from the actual `γ` maps (`physMapImageRows`), not caller-supplied — must be
    PAIRWISE DISJOINT (no two copies share a physical-qubit image). -/
def parallelDimensionJumpsOk (gammas : List PhysMap) : Bool :=
  pairwiseDisjointSupports (gammas.map physMapImageRows)

/-! ## §DJ.2. Tests. -/

/-- A trivial commuting chain-square (zero boundaries, identity `γ₁ = highMap`) over `n = 1`. -/
def djSquare : ChainMapSquare :=
  { srcBoundary := [[false]], tgtBoundary := [[false]],
    highMap := { srcN := 1, tgtN := 1, matrix := [[true]] },     -- γ₁ = identity inclusion (weight 1, rank 1)
    lowMap  := { srcN := 1, tgtN := 1, matrix := [[true]] } }
def djInduced : LogicalInjectionCert := { inducedLogicalMap := [[true]], claimedInjective := true }

example : djSquare.verifiedCheck = true := by decide                        -- ∂φ = φ∂
example : djSquare.highMap.physicallyTransversal = true := by decide        -- γ₁ weight ≤ 1
example : decide (rank djSquare.highMap.matrix = djSquare.highMap.srcN) = true := by decide  -- γ₁ non-degenerate
example : djInduced.computableInjective = true := by decide                 -- rank 1 = length 1
example : ok? (checkDimensionJump? djSquare djInduced) = true := by decide

-- NEGATIVE — a NON-INJECTIVE induced logical map (a zero row collapses a logical) is REJECTED:
def djNonInjective : LogicalInjectionCert := { inducedLogicalMap := [[true, false], [false, false]], claimedInjective := true }
example : djNonInjective.computableInjective = false := by decide           -- rank 1 ≠ length 2
example : ok? (checkDimensionJump? djSquare djNonInjective) = false := by decide

-- NEGATIVE — a ZERO γ₁ (= square.highMap = 0) paired with a FAKE injective logical cert is
-- REJECTED by the non-degeneracy gate (rank 0 ≠ srcN), even though the square still commutes:
def djZeroSquare : ChainMapSquare := { djSquare with highMap := { srcN := 1, tgtN := 1, matrix := [[false]] } }
example : djZeroSquare.verifiedCheck = true := by decide                     -- a zero map still commutes…
example : decide (rank djZeroSquare.highMap.matrix = djZeroSquare.highMap.srcN) = false := by decide  -- …but is degenerate
example : ok? (checkDimensionJump? djZeroSquare djInduced) = false := by decide

-- NEGATIVE — an UNRELATED-SIZE injective logical map (2×2, but γ₁ = highMap is 1×1) is
-- REJECTED by the dimension-compatibility gate (even though it is injective):
def djUnrelated : LogicalInjectionCert := { inducedLogicalMap := TypeChecker.idMat 2, claimedInjective := true }
example : djUnrelated.computableInjective = true := by decide                 -- rank 2 = length 2 (injective)…
example : inducedDimCompat djSquare.highMap djUnrelated = false := by decide   -- …but 2 > γ₁.srcN = 1
example : ok? (checkDimensionJump? djSquare djUnrelated) = false := by decide

-- NEGATIVE — a cert with `claimedInjective := false` is REJECTED (the flag is load-bearing,
-- must AGREE with the computed rank — not silently ignored):
def djClaimFalse : LogicalInjectionCert := { inducedLogicalMap := [[true]], claimedInjective := false }
example : djClaimFalse.computableInjective = true := by decide               -- computably injective…
example : ok? (checkDimensionJump? djSquare djClaimFalse) = false := by decide  -- …but rejected (claim false)

-- NEGATIVE — a NON-COMMUTING chain-square is REJECTED:
def djBadSquare : ChainMapSquare := { djSquare with tgtBoundary := [[true]] }
example : ok? (checkDimensionJump? djBadSquare djInduced) = false := by decide

-- NEGATIVE — a NON-TRANSVERSAL γ₁ (square.highMap with a weight-2 row) is REJECTED:
def djDenseSquare : ChainMapSquare :=
  { srcBoundary := ChainQ.GF2.zeroMat 2 2, tgtBoundary := ChainQ.GF2.zeroMat 2 2,
    highMap := { srcN := 2, tgtN := 2, matrix := [[true, true], [false, false]] },
    lowMap  := { srcN := 2, tgtN := 2, matrix := [[true, false], [false, true]] } }
example : djDenseSquare.highMap.physicallyTransversal = false := by decide
example : ok? (checkDimensionJump? djDenseSquare djInduced) = false := by decide

-- PARALLEL copies: image supports COMPUTED from the γ maps; DISJOINT accepted, OVERLAPPING rejected:
def djG1 : PhysMap := { srcN := 1, tgtN := 2, matrix := [[true], [false]] }   -- image rows {0}
def djG2 : PhysMap := { srcN := 1, tgtN := 2, matrix := [[false], [true]] }   -- image rows {1}
example : parallelDimensionJumpsOk [djG1, djG2] = true := by decide
example : parallelDimensionJumpsOk [djG1, djG1] = false := by decide          -- both image {0} — overlap

end Compiler.CodeSwitch
