/-
  ChainQ.HGPCode.Checked — the checked hypergraph-product constructor and its
  executable accept/reject tests.

  Split out of `ChainQ.Checked`; bodies copied verbatim.
-/
import ChainQ.Checked.Basic
import ChainQ.HGPCode.Basic
import ChainQ.HGPCode.Repetition

namespace ChainQ
open ChainQ.GF2

/-! ## §2. Checked constructors — `Except ChainQError CheckedCSSCode`. -/

/-- Hypergraph product; rejects declared-vs-actual shape disagreement and any
    zero dimension. -/
def mkHGP (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : Except ChainQError CheckedCSSCode :=
  if ! (hasShape h1 m1 n1 && hasShape h2 m2 n2) then
    .error (.badDimension "HGP: a declared dimension disagrees with the actual matrix shape")
  else if ! (decide (1 ≤ m1) && decide (1 ≤ n1) && decide (1 ≤ m2) && decide (1 ≤ n2)) then
    .error (.degenerateParam "HGP: m1, n1, m2, n2 must all be ≥ 1")
  else mkCSS (Internal.hgp h1 h2 m1 n1 m2 n2)

/-! ## §4. Executable tests (separate from the theorems above). -/

-- accepts:
example : isOk (mkHGP (repOpen 3) (repOpen 3) 2 3 2 3) = true := by decide

-- rejects, with the RIGHT reason:
example : (match mkHGP (repOpen 3) (repOpen 3) 5 3 2 3 with | .error (.badDimension _) => true | _ => false) = true := by decide

end ChainQ
