/-
  ChainQ.Surface.Basic — the surface-code family (unrotated), an HGP of two open
  repetition codes, plus its checked `?`-variant.

  Split out of `ChainQ.Families`; bodies copied verbatim.
-/
import ChainQ.HGPCode.Basic
import ChainQ.HGPCode.Repetition

namespace ChainQ
open ChainQ.GF2

/-! ## §3. Named families (parametric, built on the raw constructors). -/

/-- The (unrotated) surface code at distance `d` = HGP of two open repetition
    codes: `[[d² + (d−1)², 1, d]]`. -/
def surface (d : Nat) : CSSCode := Internal.hgp (repOpen d) (repOpen d) (d - 1) d (d - 1) d

/-! ## §4. Tests — dimensions, shapes, CSS condition. -/

-- Surface code: n = d² + (d−1)².
example : (surface 2).n = 5 := by decide
example : (surface 3).n = 13 := by decide
example : (surface 2).valid = true := by decide
example : (surface 3).valid = true := by decide
example : hasShape (surface 3).hx 6 13 = true := by decide   -- 6 X-checks on 13 qubits
example : hasShape (surface 3).hz 6 13 = true := by decide

/-! ## §5. Checked constructors. -/

/-- Checked surface code: requires `d ≥ 2`. -/
def surface? (d : Nat) : Option CSSCode := if 2 ≤ d then some (surface d) else none

example : (surface? 3).isSome = true := by decide
example : (surface? 1) = none := by decide                                   -- d < 2 rejected

end ChainQ
