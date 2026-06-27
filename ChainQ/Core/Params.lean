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
  orthogonal b.lx c.hz && orthogonal b.lz c.hx &&
  b.lx.all (fun r => ! inSpan c.hx r) &&
  b.lz.all (fun r => ! inSpan c.hz r) &&
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
example : (CSSLogicalBasis.mk [[true]] [[true]]).valid bareQubit = true := by decide
-- wrong width (lx is 1×2, not 1×1) → rejected, not silently truncated:
example : (CSSLogicalBasis.mk [[true, false]] [[true]]).valid bareQubit = false := by decide
-- wrong pairing (Z̄ = I, so dotBit(X̄,Z̄) = 0 ≠ 1) → rejected:
example : (CSSLogicalBasis.mk [[true]] [[false]]).valid bareQubit = false := by decide

/-- A 1-stabilizer code `[[2,1,1]]` (X-check `XX`): `X̄ = X₀`, `Z̄ = Z₀Z₁`. -/
def xCheck2 : CSSCode := { n := 2, hx := [[true, true]], hz := [] }

example : xCheck2.k = 1 := by decide
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
example : deriveLogicalBasis? badCode = none := by decide
-- the empty basis is shape-OK but the CODE is invalid → rejected by the `c.valid` guard:
example : (CSSLogicalBasis.mk [] []).valid badCode = false := by decide

/-- A ragged code (an `hx` row of length 2 ≠ n = 3). -/
def raggedCode : CSSCode := { n := 3, hx := [[true, true]], hz := [] }
example : raggedCode.valid = false := by decide
example : deriveLogicalBasis? raggedCode = none := by decide

end ChainQ
