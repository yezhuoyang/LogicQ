/-
  ChainQ.Error — the error vocabulary for ChainQ's CHECKED constructors.

  Public ChainQ code-object constructors return `Except ChainQError _` (not bare
  `Option`), so a rejection carries WHY it was rejected.  This is the front-end
  analogue of `TypeChecker.TypeError`.
-/

namespace ChainQ

/-- Why a checked ChainQ constructor rejected its input. -/
inductive ChainQError
  | badDimension              (msg : String)   -- a declared shape disagrees with the actual matrix
  | degenerateParam           (msg : String)   -- a parameter for which the family formula is meaningless (d<2, ℓ=0, …)
  | invalidCSS                (msg : String)   -- ragged check matrix or `Hx·Hzᵀ ≠ 0`
  | logicalDerivationFailed   (msg : String)   -- `deriveLogicalBasis?` could not produce a valid basis
  | other                     (msg : String)
  deriving Repr, DecidableEq

end ChainQ
