/-
  ChainQ.Materialize.Basic — the CSS materialization / export API (M20 Part B).

  EXACT MEANING (read before trusting this):
    * ChainQ family constructors (`surface`/`toric`/`mkHGP`/`mkBB`/`mkLiftedProduct`)
      are NOT symbolic placeholders.  For FIXED parameters they compute CONCRETE
      GF(2) check matrices — `hx`, `hz` are honest `BoolMat` values you can `#eval`.
    * This module exposes the front-end accessors that turn a `CSSCode` into its
      concrete check / stabilizer matrices:
        - `CSSCode.xChecks`  = the X-check matrix `hx`  (rows over `n` data qubits)
        - `CSSCode.zChecks`  = the Z-check matrix `hz`
        - `CSSCode.checkMatrices` = the pair `(hx, hz)`
        - `CSSCode.symplecticStabilizers` = the width-`2n` symplectic stabilizer matrix:
          each X-check row `r` becomes `r ++ 0ⁿ`, each Z-check row `r` becomes `0ⁿ ++ r`,
          X-rows first then Z-rows.  This is exactly the convention `TypeChecker` uses
          for `Block.stab` (the former `TypeChecker.cssToStab`, now re-exported as a thin
          alias of this function — the FRONT-END owns the CSS→stabilizer path).
    * The "COMPLETE STABILIZER SET" means the generated stabilizer-check rows `Hx`/`Hz`
      (the rows of `symplecticStabilizers`); REDUNDANT generators are allowed (we do not
      claim independence/minimality).
    * Code DISTANCE and FAULT-TOLERANCE remain OUT OF SCOPE.
-/
import ChainQ.Code

namespace ChainQ
open ChainQ.GF2

/-- The X-check (parity) matrix: `hx`, rows over the `n` data qubits. -/
def CSSCode.xChecks (c : CSSCode) : BoolMat := c.hx

/-- The Z-check (parity) matrix: `hz`. -/
def CSSCode.zChecks (c : CSSCode) : BoolMat := c.hz

/-- Both check matrices as the pair `(hx, hz)`. -/
def CSSCode.checkMatrices (c : CSSCode) : BoolMat × BoolMat := (c.hx, c.hz)

/-- The complete symplectic stabilizer-check matrix (width `2·n`): each X-check row
    `r` (width `n`) is laid out as `r ++ 0ⁿ`, each Z-check row `r` as `0ⁿ ++ r`, with
    all X-rows before all Z-rows.  Row count = `hx.length + hz.length`; this is the
    canonical CSS→stabilizer materialization (= the former `cssToStab`). -/
def CSSCode.symplecticStabilizers (c : CSSCode) : BoolMat :=
  c.hx.map (fun row => row ++ List.replicate c.n false) ++
  c.hz.map (fun row => List.replicate c.n false ++ row)

end ChainQ
