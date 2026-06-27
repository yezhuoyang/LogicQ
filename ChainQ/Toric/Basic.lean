/-
  ChainQ.Toric.Basic — the toric-code family, an HGP of two cyclic repetition
  codes, plus its checked `?`-variant.

  Split out of `ChainQ.Families`; bodies copied verbatim.
-/
import ChainQ.HGPCode.Basic
import ChainQ.HGPCode.Repetition

namespace ChainQ
open ChainQ.GF2

/-! ## §3. Named families (parametric, built on the raw constructors). -/

/-- The toric code at distance `d` = HGP of two cyclic repetition codes:
    `[[2d², 2, d]]`. -/
def toric (d : Nat) : CSSCode := Internal.hgp (repCyc d) (repCyc d) d d d d

/-! ## §4. Tests — dimensions, shapes, CSS condition. -/

-- Toric code: n = 2d².
example : (toric 3).n = 18 := by decide
example : (toric 3).valid = true := by decide
example : (toric 2).valid = true := by decide

/-! ## §5. Checked constructors. -/

/-- Checked toric code: requires `d ≥ 2`. -/
def toric? (d : Nat) : Option CSSCode := if 2 ≤ d then some (toric d) else none

example : (toric? 2).isSome = true := by decide
example : (toric? 0) = none := by decide

end ChainQ
