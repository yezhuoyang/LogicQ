/-
  ChainQ.Surface.Checked — the checked surface-code constructor, its soundness
  theorem, and the executable tests (including the full checked pipeline).

  Split out of `ChainQ.Checked`; bodies copied verbatim.
-/
import ChainQ.Checked.Basic
import ChainQ.Surface.Basic

namespace ChainQ
open ChainQ.GF2

/-! ## §2. Checked constructors — `Except ChainQError CheckedCSSCode`. -/

/-- Surface code `[[d²+(d−1)², 1, d]]`; rejects the degenerate `d < 2`. -/
def mkSurface (d : Nat) : Except ChainQError CheckedCSSCode :=
  if d < 2 then .error (.degenerateParam "surface code needs d ≥ 2")
  else mkCSS (surface d)

/-! ## §3. Constructor soundness (∀-theorems, not `decide` examples). -/

/-- A successful `mkSurface` yields exactly `surface d`, and it is valid. -/
theorem mkSurface_sound {d : Nat} {cc : CheckedCSSCode} (h : mkSurface d = .ok cc) :
    cc.code = surface d ∧ cc.code.valid = true := by
  unfold mkSurface at h
  split at h
  · contradiction
  · exact ⟨mkCSS_sound h, cc.valid⟩

/-! ## §4. Executable tests (separate from the theorems above). -/

-- accepts:
example : isOk (mkSurface 3) = true := by decide

-- rejects, with the RIGHT reason:
example : (match mkSurface 1 with | .error (.degenerateParam _) => true | _ => false) = true := by decide

-- the full checked pipeline: build surface(2), then derive its logical basis.
example : (match mkSurface 2 with | .ok cc => isOk (mkLogicalBasis cc) | _ => false) = true := by decide

end ChainQ
