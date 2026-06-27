/-
  ChainQ.HGPCode.Basic — the hypergraph-product raw constructor and its checked
  `?`-variant (Tillich–Zémor, arXiv 0903.0566).

  Split out of `ChainQ.Families`; bodies copied verbatim.
-/
import ChainQ.Shape
import ChainQ.Code
import ChainQ.HGPCode.Repetition

namespace ChainQ
open ChainQ.GF2

/-! ## §2. RAW product constructors (⚠ INTERNAL, shape-unchecked). -/
namespace Internal

/-- HGP of classical `h1` (`m1×n1`) and `h2` (`m2×n2`):
    `hx = [h1⊗I_{n2} | I_{m1}⊗h2ᵀ]`, `hz = [I_{n1}⊗h2 | h1ᵀ⊗I_{m2}]`,
    `n = n1·n2 + m1·m2`.  Satisfies `hx·hzᵀ = h1⊗h2ᵀ + h1⊗h2ᵀ = 0`. -/
def hgp (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : CSSCode :=
  { n  := n1 * n2 + m1 * m2,
    hx := hcat (kron h1 (identMat n2)) (kron (identMat m1) (transpose h2 n2)),
    hz := hcat (kron (identMat n1) h2) (kron (transpose h1 n1) (identMat m2)) }

end Internal

/-! ## §5. Checked constructors. -/

/-- Checked HGP: `none` unless the declared shapes match the actual matrices and
    every dimension is ≥ 1. -/
def hgp? (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : Option CSSCode :=
  if hasShape h1 m1 n1 && hasShape h2 m2 n2 &&
     decide (1 ≤ m1) && decide (1 ≤ n1) && decide (1 ≤ m2) && decide (1 ≤ n2)
  then some (Internal.hgp h1 h2 m1 n1 m2 n2) else none

example : (hgp? (repOpen 3) (repOpen 3) 2 3 2 3).isSome = true := by decide   -- declared = actual
example : (hgp? (repOpen 3) (repOpen 3) 5 3 2 3) = none := by decide          -- declared m1=5 ≠ actual 2

end ChainQ
