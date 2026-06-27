/-
  ChainQ.Ring — the circulant group-ring F₂[x]/(xˡ−1) over the GF(2) kernel.

  This is the one new ALGEBRAIC primitive the lifted-product / bivariate-bicycle
  families need (the review's "explicit algebraic primitive, e.g.
  polynomial/cyclic/group-ring matrices over F₂ and binary expansion").  A ring
  element is its exponent support `Circ = List Nat`; a ring-valued matrix lifts
  to a binary `BoolMat` of circulant blocks (`liftMat`).  Mathlib-free.

  Grounded in: Panteleev–Kalachev, *Quantum LDPC Codes with Almost Linear
  Minimum Distance* (arXiv 2012.04068), §4.1–4.3 (lifted product, conjugate
  transpose `a ↦ a(x⁻¹)`); and the bivariate-bicycle construction used in
  *Universal adapters between qLDPC codes* (arXiv 2410.03628).
-/
import ChainQ.Algebra.Shape

namespace ChainQ.GF2

/-! ## §1. Cyclic-shift matrices (for the bivariate ring x = Sₗ⊗Iₘ, y = Iₗ⊗Sₘ). -/

/-- `Sₗᵏ`: the `ℓ×ℓ` matrix with a `1` at `(i, (i+k) mod ℓ)`. -/
def shiftPow (l k : Nat) : BoolMat :=
  (List.range l).map (fun i => (List.range l).map (fun j => decide (j = (i + k) % l)))

/-- Entry-wise GF(2) sum (XOR) of two equal-shape matrices. -/
def matXor (A B : BoolMat) : BoolMat :=
  (A.zip B).map (fun p => (p.1.zip p.2).map (fun q => xor q.1 q.2))

/-- A bivariate monomial sum `Σ x^i y^j` over `F₂[x,y]/(xˡ−1, yᵐ−1)`, as the
    `ℓm×ℓm` binary matrix `Σ (Sₗ^i ⊗ Sₘ^j)`. -/
def biCirculant (l m : Nat) (terms : List (Nat × Nat)) : BoolMat :=
  terms.foldl (fun acc t => matXor acc (kron (shiftPow l t.1) (shiftPow m t.2)))
    (zeroMat (l * m) (l * m))

/-! ## §2. The circulant ring R = F₂[x]/(xˡ−1) by exponent support. -/

/-- A ring element of `F₂[x]/(xˡ−1)`, as a multiset of exponents.  The
    representation is NOT unique — `canonicalize` fixes the GF(2) semantics. -/
abbrev Circ := List Nat

/-- **Canonical support** mod `ℓ`: the exponents (taken mod `ℓ`) of ODD
    multiplicity (GF(2) duplicate cancellation).  This is the single source of
    truth: `[0,0]` ↦ `[]` (the ZERO element), `[0]` ↦ `[0]` (the identity `1`),
    `[ℓ]` ↦ `[0]`.  Every ring operation below routes through it. -/
def circNorm (l : Nat) (p : Circ) : Circ :=
  (List.range l).filter (fun e => (p.countP (fun x => x % l = e)) % 2 = 1)

/-- Lift a ring element to its `ℓ×ℓ` circulant binary matrix.  Canonicalizes
    first, so a duplicated exponent cancels (it does NOT become a stray `1`). -/
def circulant (l : Nat) (p : Circ) : BoolMat :=
  let s := circNorm l p
  (List.range l).map (fun i =>
    (List.range l).map (fun j => s.contains ((j + l - i % l) % l)))

/-- The ring antipode/conjugate `a ↦ a(x⁻¹)`: exponent `e ↦ (ℓ−e) mod ℓ`,
    canonicalized.  Satisfies `transpose (circulant ℓ p) = circulant ℓ (circDagger ℓ p)`. -/
def circDagger (l : Nat) (p : Circ) : Circ :=
  circNorm l (p.map (fun e => (l - e % l) % l))

/-- Ring multiplication in `F₂[x]/(xˡ−1)`: convolution of supports mod `ℓ`,
    keeping odd-multiplicity exponents (mod-2 sum). -/
def circMul (l : Nat) (p q : Circ) : Circ :=
  let prods := p.flatMap (fun i => q.map (fun j => (i + j) % l))
  (List.range l).filter (fun e => prods.countP (fun x => x = e) % 2 = 1)

/-! ## §3. Ring-valued matrices and their binary lift. -/

/-- The `n×n` ring identity (`1 = x⁰` on the diagonal, `0 = []` off it). -/
def pIdent (n : Nat) : List (List Circ) :=
  (List.range n).map (fun i => (List.range n).map (fun j => if i = j then ([0] : Circ) else []))

/-- Conjugate transpose of a ring matrix (transpose the grid, conjugate each entry). -/
def pDagger (l : Nat) (A : List (List Circ)) : List (List Circ) :=
  let r := A.length
  let c := (A.headD []).length
  (List.range c).map (fun j => (List.range r).map (fun i => circDagger l ((A.getD i []).getD j [])))

/-- Kronecker (tensor) product of two ring matrices (block `(i,k),(j,l)` is the
    ring product of `A[i][j]` and `B[k][l]`). -/
def pKron (l : Nat) (A B : List (List Circ)) : List (List Circ) :=
  A.flatMap (fun arow => B.map (fun brow =>
    arow.flatMap (fun a => brow.map (fun b => circMul l a b))))

/-- Horizontal block concatenation of two same-row-count ring matrices. -/
def pHcat (L R : List (List Circ)) : List (List Circ) := L.zipWith (· ++ ·) R

/-- Lift an `r×c` ring matrix to its `rℓ × cℓ` binary matrix of circulant blocks. -/
def liftMat (l : Nat) (A : List (List Circ)) : BoolMat :=
  A.flatMap (fun polyRow =>
    let blocks := polyRow.map (fun e => circulant l e)
    (List.range l).map (fun r => blocks.flatMap (fun blk => blk.getD r [])))

/-! ## §4. Smoke checks (ring laws). -/

-- the conjugate of a circulant is its transpose (the key fact behind the CSS condition)
example : circulant 3 (circDagger 3 [1]) = transpose (circulant 3 [1]) 3 := by decide
example : circulant 4 (circDagger 4 [1, 2]) = transpose (circulant 4 [1, 2]) 4 := by decide
-- `x · x⁻¹ = 1`
example : circMul 5 [1] [4] = [0] := by decide
-- a circulant has the right shape
example : hasShape (circulant 3 [0, 1]) 3 3 = true := by decide

-- CANONICALIZATION REGRESSIONS (GF(2) duplicate cancellation):
example : circNorm 3 [0, 0] = [] := by decide               -- 1 + 1 = 0
example : circNorm 3 [0] = [0] := by decide                 -- the identity
example : circNorm 3 [1, 1, 1] = [1] := by decide           -- 3·x ≡ x
example : circNorm 3 [3] = [0] := by decide                 -- x³ ≡ 1 (mod x³−1)
-- the crucial regression: `[0,0]` is ZERO, not the identity
example : circulant 3 [0, 0] = zeroMat 3 3 := by decide
example : circulant 3 [0] = identMat 3 := by decide
example : circulant 3 [3] = identMat 3 := by decide         -- exponent reduced mod ℓ
-- circMul cancels duplicates (x·x + x·x = 0)
example : circMul 3 [1, 1] [1] = [] := by decide

end ChainQ.GF2
