/-
  ChainQ.Materialize.Tests — concrete materialization tests (M20 Part B).

  These prove the family constructors compute CONCRETE GF(2) matrices for fixed
  parameters (not symbolic placeholders): exact surface-2 `Hx`/`Hz`, surface-3 shape,
  the surface-2 symplectic stabilizer matrix (4 rows × width 10), `mkSurface 2` giving
  the same concrete matrices, and materialization smoke tests across all five families.
-/
import ChainQ.Materialize.Basic
import ChainQ.Families
import ChainQ.Checked

namespace ChainQ
open ChainQ.GF2

/-! ## §1. Exact surface-2 check matrices (n = 5). -/

example : (surface 2).n = 5 := by decide
example : (surface 2).xChecks = [[true, false, true, false, true], [false, true, false, true, true]] := by decide
example : (surface 2).zChecks = [[true, true, false, false, true], [false, false, true, true, true]] := by decide
example : (surface 2).checkMatrices = ((surface 2).hx, (surface 2).hz) := by decide
example : (surface 2).xChecks.length = 2 := by decide
example : (surface 2).zChecks.length = 2 := by decide

/-! ## §2. Surface-3 shape: n = 13, hx/hz each 6 rows of width 13. -/

example : (surface 3).n = 13 := by decide
example : hasShape (surface 3).xChecks 6 13 = true := by decide
example : hasShape (surface 3).zChecks 6 13 = true := by decide

/-! ## §3. Surface-2 symplectic stabilizer matrix: hx.length + hz.length = 4 rows, width 2n = 10. -/

example : (surface 2).symplecticStabilizers =
  [[true, false, true, false, true, false, false, false, false, false],
   [false, true, false, true, true, false, false, false, false, false],
   [false, false, false, false, false, true, true, false, false, true],
   [false, false, false, false, false, false, false, true, true, true]] := by decide
example : (surface 2).symplecticStabilizers.length = 4 := by decide
example : (surface 2).symplecticStabilizers.length
        = (surface 2).xChecks.length + (surface 2).zChecks.length := by decide
example : hasShape (surface 2).symplecticStabilizers 4 10 = true := by decide   -- 4 rows, width 2·n = 10

/-! ## §4. `mkSurface 2` returns the same concrete matrices (checked = raw). -/

example : (match mkSurface 2 with
           | .ok cc => decide (cc.code.checkMatrices = (surface 2).checkMatrices)
           | .error _ => false) = true := by decide
example : (match mkSurface 2 with
           | .ok cc => decide (cc.code.symplecticStabilizers = (surface 2).symplecticStabilizers)
           | .error _ => false) = true := by decide

/-! ## §5. Materialization smoke tests across families: the symplectic matrix has
    `xChecks.length + zChecks.length` rows, each of width `2·n` (well-shaped). -/

-- toric 2 (n = 8)
example : hasShape (toric 2).symplecticStabilizers
            ((toric 2).xChecks.length + (toric 2).zChecks.length) (2 * (toric 2).n) = true := by decide
-- HGP (repOpen 3 × repOpen 2, n = 8)
example : hasShape (Internal.hgp (repOpen 3) (repOpen 2) 2 3 1 2).symplecticStabilizers
            ((Internal.hgp (repOpen 3) (repOpen 2) 2 3 1 2).xChecks.length
              + (Internal.hgp (repOpen 3) (repOpen 2) 2 3 1 2).zChecks.length)
            (2 * (Internal.hgp (repOpen 3) (repOpen 2) 2 3 1 2).n) = true := by decide
-- bivariate bicycle (ℓ=m=2, n = 8)
example : hasShape (Internal.bb 2 2 [(0,0),(1,0)] [(0,0),(0,1)]).symplecticStabilizers
            ((Internal.bb 2 2 [(0,0),(1,0)] [(0,0),(0,1)]).xChecks.length
              + (Internal.bb 2 2 [(0,0),(1,0)] [(0,0),(0,1)]).zChecks.length)
            (2 * (Internal.bb 2 2 [(0,0),(1,0)] [(0,0),(0,1)]).n) = true := by decide
-- lifted product (ℓ=2, n = 10)
example : hasShape (Internal.liftedProduct 2 [[[0],[1]]] 1 2).symplecticStabilizers
            ((Internal.liftedProduct 2 [[[0],[1]]] 1 2).xChecks.length
              + (Internal.liftedProduct 2 [[[0],[1]]] 1 2).zChecks.length)
            (2 * (Internal.liftedProduct 2 [[[0],[1]]] 1 2).n) = true := by decide

end ChainQ
