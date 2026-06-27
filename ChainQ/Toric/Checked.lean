/-
  ChainQ.Toric.Checked — the checked toric-code constructor, its soundness
  theorem, and the executable accept test.

  Split out of `ChainQ.Checked`; bodies copied verbatim.
-/
import ChainQ.Checked.Basic
import ChainQ.Toric.Basic

namespace ChainQ
open ChainQ.GF2

/-! ## §2. Checked constructors — `Except ChainQError CheckedCSSCode`. -/

/-- Toric code `[[2d², 2, d]]`; rejects `d < 2`. -/
def mkToric (d : Nat) : Except ChainQError CheckedCSSCode :=
  if d < 2 then .error (.degenerateParam "toric code needs d ≥ 2")
  else mkCSS (toric d)

/-! ## §3. Constructor soundness (∀-theorems, not `decide` examples). -/

/-- A successful `mkToric` yields exactly `toric d`, and it is valid. -/
theorem mkToric_sound {d : Nat} {cc : CheckedCSSCode} (h : mkToric d = .ok cc) :
    cc.code = toric d ∧ cc.code.valid = true := by
  unfold mkToric at h
  split at h
  · contradiction
  · exact ⟨mkCSS_sound h, cc.valid⟩

/-! ## §4. Executable tests (separate from the theorems above). -/

-- accepts:
example : isOk (mkToric 2) = true := by decide

end ChainQ
