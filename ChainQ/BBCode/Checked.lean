/-
  ChainQ.BBCode.Checked — the checked bivariate-bicycle constructor and its
  executable accept/reject tests.

  Split out of `ChainQ.Checked`; bodies copied verbatim.
-/
import ChainQ.Checked.Basic
import ChainQ.BBCode.Basic

namespace ChainQ
open ChainQ.GF2

/-! ## §2. Checked constructors — `Except ChainQError CheckedCSSCode`. -/

/-- Bivariate bicycle; rejects `ℓ = 0`, `m = 0`, or empty `A`/`B`. -/
def mkBB (l m : Nat) (a b : List (Nat × Nat)) : Except ChainQError CheckedCSSCode :=
  if ! (decide (1 ≤ l) && decide (1 ≤ m)) then
    .error (.degenerateParam "BB: ℓ and m must be ≥ 1")
  else if a.isEmpty || b.isEmpty then
    .error (.degenerateParam "BB: A and B must be nonempty")
  else mkCSS (Internal.bb l m a b)

/-! ## §4. Executable tests (separate from the theorems above). -/

-- accepts:
example : isOk (mkBB 3 3 [(0,0),(1,0),(0,2)] [(0,0),(2,0),(0,1)]) = true := by decide

-- rejects, with the RIGHT reason:
example : (match mkBB 0 3 [(0,0)] [(0,0)] with | .error (.degenerateParam _) => true | _ => false) = true := by decide

end ChainQ
