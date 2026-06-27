/-
  ChainQ.Checked.Basic — the SHARED base of the typed ChainQ front-end core.

  A well-formed code object is a value of a type that CARRIES its validity proof:
    * `CheckedCSSCode`      — a `CSSCode` with `code.valid = true`;
    * `CheckedLogicalBasis` — a `CSSCode` + `CSSLogicalBasis` with the basis valid.
  Public constructors return `Except ChainQError _`.

  Split out of `ChainQ.Checked`; bodies copied verbatim.
-/
import ChainQ.Params
import ChainQ.Error

namespace ChainQ
open ChainQ.GF2

/-! ## §1. Validated code objects (invariant carried in the type). -/

/-- A CSS code together with a PROOF it is well-typed.  Sound by construction:
    no `CheckedCSSCode` exists whose `code` is invalid. -/
structure CheckedCSSCode where
  code  : CSSCode
  valid : code.valid = true

/-- A CSS code with a logical basis, together with a proof the basis is valid. -/
structure CheckedLogicalBasis where
  code  : CSSCode
  basis : CSSLogicalBasis
  valid : CSSLogicalBasis.valid code basis = true

/-- Did a checked constructor succeed? (a Bool view for `decide` tests). -/
def isOk {ε α : Type} : Except ε α → Bool
  | .ok _    => true
  | .error _ => false

/-! ## §2. Checked constructors — `Except ChainQError CheckedCSSCode`. -/

/-- Validate an arbitrary `CSSCode`, packaging the validity proof. -/
def mkCSS (c : CSSCode) : Except ChainQError CheckedCSSCode :=
  if h : c.valid = true then .ok ⟨c, h⟩
  else if c.wellShaped then .error (.invalidCSS "Hx·Hzᵀ ≠ 0 (X- and Z-checks anticommute)")
  else .error (.invalidCSS "ragged check matrix (a row's length ≠ n)")

/-- Derive AND validate a logical basis for a checked code (via the sound
    `deriveLogicalBasis?`).  The proof is supplied by `deriveLogicalBasis?_sound`. -/
def mkLogicalBasis (cc : CheckedCSSCode) : Except ChainQError CheckedLogicalBasis :=
  match h : deriveLogicalBasis? cc.code with
  | some bas => .ok ⟨cc.code, bas, deriveLogicalBasis?_sound h⟩
  | none     => .error (.logicalDerivationFailed "no valid logical basis could be derived")

/-! ## §3. Constructor soundness (∀-theorems, not `decide` examples). -/

/-- The invariant is in the type: every `CheckedCSSCode` has a valid code. -/
theorem CheckedCSSCode.code_valid (cc : CheckedCSSCode) : cc.code.valid = true := cc.valid

/-- `mkCSS` round-trips: a success returns exactly the input code (already valid). -/
theorem mkCSS_sound {c : CSSCode} {cc : CheckedCSSCode} (h : mkCSS c = .ok cc) :
    cc.code = c := by
  unfold mkCSS at h
  split at h
  · injection h with h'; subst h'; rfl
  · split at h <;> contradiction

/-- `mkLogicalBasis` is sound: a success returns the SAME code with exactly the
    basis that `deriveLogicalBasis?` derived (which validates, by
    `deriveLogicalBasis?_sound`) — a genuine fact about the constructor, not just
    the carried type invariant. -/
theorem mkLogicalBasis_sound {cc : CheckedCSSCode} {clb : CheckedLogicalBasis}
    (h : mkLogicalBasis cc = .ok clb) :
    clb.code = cc.code ∧ deriveLogicalBasis? cc.code = some clb.basis := by
  unfold mkLogicalBasis at h
  split at h
  · next bas heq => injection h with h'; subst h'; exact ⟨rfl, heq⟩
  · exact absurd h (by simp)

/-! ## §4. Executable tests (separate from the theorems above). -/

-- rejects, with the RIGHT reason:
example : (match mkCSS { n := 2, hx := [[true, false]], hz := [[true, false]] } with
           | .error (.invalidCSS _) => true | _ => false) = true := by decide

end ChainQ
