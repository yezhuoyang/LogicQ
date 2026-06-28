/-
  ChainQ.Params — CSS code parameters and logical-basis validity.

  `k` is COMPUTED from GF(2) rank (`n − rank Hx − rank Hz`), not declared.  A
  declared logical basis is checked with EXPLICIT shapes first, so a wrong
  width/row-count is rejected rather than silently zip-truncated or padded.
-/
import ChainQ.Families
import ChainQ.Algebra.GF2Rank
import ChainQ.Algebra.Kernel

namespace ChainQ
open ChainQ.GF2

/-- Number of logical qubits, computed from rank: `k = n − rank(Hx) − rank(Hz)`
    (Nat subtraction; the genuine value when `rank Hx + rank Hz ≤ n`, which holds
    for any `valid` CSS code). -/
def CSSCode.k (c : CSSCode) : Nat := c.n - rank c.hx - rank c.hz

/-! ## Homological logical representatives. -/

/-- A CSS Z-support is a cycle iff it commutes with every X-check. -/
def CSSCode.zCycle (c : CSSCode) (z : BoolVec) : Bool :=
  decide (z.length = c.n) && c.hx.all (fun x => !dotBit x z)

/-- A CSS Z-support is a boundary iff it is a product of Z-checks. -/
def CSSCode.zBoundary (c : CSSCode) (z : BoolVec) : Bool := inSpan c.hz z

/-- A nontrivial logical Z representative: a cycle in `ker Hx` that is not a
    Z-stabilizer in `rowSpan Hz`. -/
def CSSCode.logicalZ (c : CSSCode) (z : BoolVec) : Bool :=
  c.valid && c.zCycle z && !c.zBoundary z

/-- Preferred user-facing name for `logicalZ`: this checks a nonzero quotient-class
    representative, not a chosen coordinate-basis operator. -/
def CSSCode.isNontrivialZLogicalRep (c : CSSCode) (z : BoolVec) : Bool := c.logicalZ z

/-- A CSS X-support is a cycle iff it commutes with every Z-check. -/
def CSSCode.xCycle (c : CSSCode) (x : BoolVec) : Bool :=
  decide (x.length = c.n) && c.hz.all (fun z => !dotBit x z)

/-- A CSS X-support is a boundary iff it is a product of X-checks. -/
def CSSCode.xBoundary (c : CSSCode) (x : BoolVec) : Bool := inSpan c.hx x

/-- A nontrivial logical X representative: a cycle in `ker Hz` that is not an
    X-stabilizer in `rowSpan Hx`. -/
def CSSCode.logicalX (c : CSSCode) (x : BoolVec) : Bool :=
  c.valid && c.xCycle x && !c.xBoundary x

/-- Preferred user-facing name for `logicalX`: this checks a nonzero quotient-class
    representative, not a chosen coordinate-basis operator. -/
def CSSCode.isNontrivialXLogicalRep (c : CSSCode) (x : BoolVec) : Bool := c.logicalX x

/-- A quotient-independence check: adjoining the representatives must increase
    row-span rank by exactly their row count.  Shape is checked separately by
    callers before this rank comparison is trusted. -/
def independentModulo (stab rows : BoolMat) : Bool :=
  decide (rank (stab ++ rows) = rank stab + rows.length)

theorem independentModulo_iff_rank (stab rows : BoolMat) :
    independentModulo stab rows = true ↔ rank (stab ++ rows) = rank stab + rows.length := by
  unfold independentModulo
  simp

def CSSCode.logicalZBasisShapeAndCycle (c : CSSCode) (zs : BoolMat) : Bool :=
  hasShape zs c.k c.n &&
  zs.all (fun z => c.isNontrivialZLogicalRep z) &&
  independentModulo c.hz zs

def CSSCode.logicalXBasisShapeAndCycle (c : CSSCode) (xs : BoolMat) : Bool :=
  hasShape xs c.k c.n &&
  xs.all (fun x => c.isNontrivialXLogicalRep x) &&
  independentModulo c.hx xs

/-- Two Z-supports represent the same logical Z class iff their product differs
    by a Z-stabilizer. -/
def CSSCode.sameZLogicalClass (c : CSSCode) (z₁ z₂ : BoolVec) : Bool :=
  decide (z₁.length = c.n) &&
  decide (z₂.length = c.n) &&
  inSpan c.hz (vecXor z₁ z₂)

/-- Two X-supports represent the same logical X class iff their product differs
    by an X-stabilizer. -/
def CSSCode.sameXLogicalClass (c : CSSCode) (x₁ x₂ : BoolVec) : Bool :=
  decide (x₁.length = c.n) &&
  decide (x₂.length = c.n) &&
  inSpan c.hx (vecXor x₁ x₂)

private theorem notBool_true_eq_false (b : Bool) : (!b) = true ↔ b = false := by
  cases b <;> simp

private theorem notBool_true_iff_not (b : Bool) : (!b) = true ↔ ¬ b = true := by
  cases b <;> simp

theorem CSSCode.logicalZ_iff (c : CSSCode) (z : BoolVec) :
    c.logicalZ z = true ↔
      c.valid = true ∧
      z.length = c.n ∧
      (∀ x ∈ c.hx, dotBit x z = false) ∧
      ¬ inSpan c.hz z := by
  unfold CSSCode.logicalZ CSSCode.zCycle CSSCode.zBoundary
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2.1, by
      intro x hx
      exact (notBool_true_eq_false (dotBit x z)).mp (h.1.2.2 x hx),
      (notBool_true_eq_false (inSpan c.hz z)).mp h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1, by
      intro x hx
      exact (notBool_true_eq_false (dotBit x z)).mpr (h.2.2.1 x hx)⟩,
      (notBool_true_eq_false (inSpan c.hz z)).mpr h.2.2.2⟩

theorem CSSCode.logicalX_iff (c : CSSCode) (x : BoolVec) :
    c.logicalX x = true ↔
      c.valid = true ∧
      x.length = c.n ∧
      (∀ z ∈ c.hz, dotBit x z = false) ∧
      ¬ inSpan c.hx x := by
  unfold CSSCode.logicalX CSSCode.xCycle CSSCode.xBoundary
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2.1, by
      intro z hz
      exact (notBool_true_eq_false (dotBit x z)).mp (h.1.2.2 z hz),
      (notBool_true_eq_false (inSpan c.hx x)).mp h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1, by
      intro z hz
      exact (notBool_true_eq_false (dotBit x z)).mpr (h.2.2.1 z hz)⟩,
      (notBool_true_eq_false (inSpan c.hx x)).mpr h.2.2.2⟩

/-- A declared logical basis: `k` X-logicals and `k` Z-logicals, each a length-`n`
    bit support (an X-type resp. Z-type Pauli over the `n` physical qubits). -/
structure CSSLogicalBasis where
  lx : BoolMat
  lz : BoolMat
  deriving Repr, Inhabited

/-- **Logical-basis well-formedness** against CSS code `c`.  The CODE itself must
    be valid (`c.valid`), and the shape checks come FIRST (so a wrong dimension
    or a malformed code is rejected, never silently truncated):
    0. `c` is a valid CSS code (well-shaped + `Hx·Hzᵀ=0`);
    1. `lx`, `lz` are exactly `k × n`;
    2. X-logicals commute with Z-stabilizers (`lx ⟂ hz`) and Z-logicals with
       X-stabilizers (`lz ⟂ hx`);
    3. each logical is NOT in its stabilizer span (genuinely logical);
    4. the X/Z pairing is the standard symplectic one: `dotBit(lxᵢ, lzⱼ) = [i=j]`,
       i.e. `gemmT lx lz = I_k`. -/
def CSSLogicalBasis.valid (c : CSSCode) (b : CSSLogicalBasis) : Bool :=
  c.valid &&
  hasShape b.lx c.k c.n && hasShape b.lz c.k c.n &&
  b.lx.all (fun r => c.logicalX r) &&
  b.lz.all (fun r => c.logicalZ r) &&
  independentModulo c.hx b.lx &&
  independentModulo c.hz b.lz &&
  decide (gemmT b.lx b.lz = identMat c.k)

/-- **Derive** a canonical logical basis for a CSS code: X-logicals from
    `ker(Hz) / rowSpan(Hx)`, Z-logicals from `ker(Hx) / rowSpan(Hz)`, dualized so
    that `gemmT lx lz = I_k`.  Returns `some` ONLY when `c` is valid and the
    produced basis passes `CSSLogicalBasis.valid` (so the result is always a
    genuine, checked basis — never a silently-wrong one). -/
def deriveLogicalBasis? (c : CSSCode) : Option CSSLogicalBasis :=
  if ! c.valid then none
  else
    -- use the SHAPE-CHECKED wrappers (not the `Unsafe.*` raw helpers): early
    -- shape rejection, per `ChainQ.Kernel`'s stated boundary rule.
    match quotientBasis? c.hx (kernelBasis c.hz c.n),      -- ker Hz, mod rowSpan Hx
          quotientBasis? c.hz (kernelBasis c.hx c.n) with  -- ker Hx, mod rowSpan Hz
    | some xLogs, some zLogs =>
      match gf2Inv? (gemmT xLogs zLogs) xLogs.length with
      | some Pinv =>
        let lz := matMul (transpose Pinv xLogs.length) zLogs c.n
        let b : CSSLogicalBasis := { lx := xLogs, lz := lz }
        if b.valid c then some b else none
      | none => none                                         -- pairing not square/invertible
    | _, _ => none

/-- **Soundness of `deriveLogicalBasis?`** (a real ∀-theorem, not a `decide`
    example): whenever the derivation returns a basis, that basis genuinely
    passes `CSSLogicalBasis.valid` for the code — the result is never a
    silently-wrong basis.  (Follows because `deriveLogicalBasis?` only emits
    `some b` through the guarded `if b.valid c then some b else none` branch.) -/
theorem deriveLogicalBasis?_sound {c : CSSCode} {b : CSSLogicalBasis}
    (h : deriveLogicalBasis? c = some b) : CSSLogicalBasis.valid c b = true := by
  simp only [deriveLogicalBasis?] at h
  -- peel the `if ! c.valid`, the two `quotientBasis?` matches, the `gf2Inv?`
  -- match, and the final `if b.valid c`; only the guarded `some b` branch survives.
  repeat (split at h <;> first | contradiction | skip)
  simp_all

/-! ## Tests: derived parameters against known small examples. -/

-- Surface code [[d²+(d−1)², 1, d]]: k = 1.
example : (surface 2).k = 1 := by decide
example : (surface 3).k = 1 := by decide
-- Toric code [[2d², 2, d]]: k = 2.
example : (toric 2).k = 2 := by decide
example : (toric 3).k = 2 := by decide

/-! ## Tests: logical-basis validity (and negatives). -/

/-- A bare logical qubit (no stabilizers): `k = 1`, `X̄ = X`, `Z̄ = Z`. -/
def bareQubit : CSSCode := { n := 1, hx := [], hz := [] }

example : bareQubit.k = 1 := by decide
example : bareQubit.logicalZ [true] = true := by decide
example : bareQubit.isNontrivialZLogicalRep [true] = true := by decide
example : bareQubit.logicalX [true] = true := by decide
example : bareQubit.isNontrivialXLogicalRep [true] = true := by decide
example : (CSSLogicalBasis.mk [[true]] [[true]]).valid bareQubit = true := by decide
-- wrong width (lx is 1×2, not 1×1) → rejected, not silently truncated:
example : (CSSLogicalBasis.mk [[true, false]] [[true]]).valid bareQubit = false := by decide
-- wrong pairing (Z̄ = I, so dotBit(X̄,Z̄) = 0 ≠ 1) → rejected:
example : (CSSLogicalBasis.mk [[true]] [[false]]).valid bareQubit = false := by decide

/-- A 1-stabilizer code `[[2,1,1]]` (X-check `XX`): `X̄ = X₀`, `Z̄ = Z₀Z₁`. -/
def xCheck2 : CSSCode := { n := 2, hx := [[true, true]], hz := [] }

example : xCheck2.k = 1 := by decide
example : xCheck2.logicalZ [true, true] = true := by decide
example : xCheck2.logicalZ [true, false] = false := by decide
example : (CSSLogicalBasis.mk [[true, false]] [[true, true]]).valid xCheck2 = true := by decide
-- a "logical" that is actually a stabilizer (X̄ = XX ∈ span hx) → rejected:
example : (CSSLogicalBasis.mk [[true, true]] [[true, true]]).valid xCheck2 = false := by decide

/-! ## Tests: DERIVED logical bases (the basis is computed, then re-checked). -/

-- `deriveLogicalBasis?` produces a (checked) basis for each small/family code:
example : (deriveLogicalBasis? bareQubit).isSome = true := by decide
example : (deriveLogicalBasis? xCheck2).isSome = true := by decide
example : (deriveLogicalBasis? (surface 2)).isSome = true := by decide
example : (deriveLogicalBasis? (toric 2)).isSome = true := by decide

/-! ## Tests: malformed codes are rejected (the `c.valid` guard). -/

/-- An invalid code: `X` and `Z` on the same qubit anticommute (`Hx·Hzᵀ ≠ 0`). -/
def badCode : CSSCode := { n := 2, hx := [[true, false]], hz := [[true, false]] }
example : badCode.valid = false := by decide
example : badCode.logicalZ [true, false] = false := by decide
example : deriveLogicalBasis? badCode = none := by decide
-- the empty basis is shape-OK but the CODE is invalid → rejected by the `c.valid` guard:
example : (CSSLogicalBasis.mk [] []).valid badCode = false := by decide

/-- A ragged code (an `hx` row of length 2 ≠ n = 3). -/
def raggedCode : CSSCode := { n := 3, hx := [[true, true]], hz := [] }
example : raggedCode.valid = false := by decide
example : raggedCode.logicalZ [false, false, true] = false := by decide
example : deriveLogicalBasis? raggedCode = none := by decide

def badNonCommutingCSS : CSSCode := { n := 1, hx := [[true]], hz := [[true]] }
example : badNonCommutingCSS.valid = false := by decide
example : badNonCommutingCSS.logicalZ [true] = false := by decide

def badRaggedCSS : CSSCode := { n := 2, hx := [[true]], hz := [] }
example : badRaggedCSS.valid = false := by decide
example : badRaggedCSS.logicalZ [false, true] = false := by decide

/-! ## Quotient-independence regression tests. -/

example : independentModulo [] [[false, false]] = false := by decide
example : independentModulo [] [[true, false], [true, false]] = false := by decide
example : independentModulo [] [[true, false], [false, true], [true, true]] = false := by decide
example : independentModulo [[true, true]] [[true, false], [false, true]] = false := by decide
example : independentModulo [[true, true]] [[true, false]] = true := by decide
example : independentModulo [] [] = true := by decide
example : independentModulo [[true, false], [true, false]] [[false, true]] = true := by decide
example : independentModulo [[true, false]] [[true, false]] = false := by decide
example : independentModulo [[true, true, false]] [[false, true, true]] = true := by decide
example : independentModulo [[true, true, false]] [[false, true, true], [true, false, true]] = false := by decide
def bareTwoForClassTests : CSSCode := { n := 2, hx := [], hz := [] }
example : bareTwoForClassTests.sameZLogicalClass [true, false] [true, false] = true := by decide
example : xCheck2.sameZLogicalClass [true, true] [false, false] = false := by decide

end ChainQ
