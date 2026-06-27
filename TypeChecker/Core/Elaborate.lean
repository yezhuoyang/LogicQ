/-
  TypeChecker.Core.Elaborate — the normal path from a ChainQ code family into the
  TypeChecker.  A `CheckedCSSCode` + `CheckedLogicalBasis` (validity-carrying,
  from ChainQ) elaborate into a symplectic `TypedBlock`: stabilizers via
  `cssToStab`, CSS logical bit-supports embedded as symplectic rows.

  The elaboration is runtime-VALIDATED (`validateBlock?` packages the
  `Block.valid` proof).  For a genuine checked CSS code + its derived basis the
  block is valid by construction; the `∀`-proof that CSS-validity ⇒ Block.valid
  (needs `rank (cssToStab c) = rank hx + rank hz` and a span-embedding lemma) is
  deferred — see DESIGN_NOTE.
-/
import TypeChecker.Core.Block

namespace TypeChecker
open ChainQ ChainQ.GF2

/-- Embed CSS X-logical bit-supports (width `n`) as symplectic rows `(lx | 0)`. -/
def embedX (n : Nat) (lx : BoolMat) : BoolMat := lx.map (fun r => r ++ List.replicate n false)

/-- Embed CSS Z-logical bit-supports (width `n`) as symplectic rows `(0 | lz)`. -/
def embedZ (n : Nat) (lz : BoolMat) : BoolMat := lz.map (fun r => List.replicate n false ++ r)

/-- Elaborate a checked CSS code + checked logical basis into a raw symplectic
    `Block` (stabilizers via `cssToStab`, logicals embedded; owned & live). -/
def elaborateBlock (cc : CheckedCSSCode) (clb : CheckedLogicalBasis) : Block :=
  { n    := cc.code.n,
    stab := cssToStab cc.code,
    lx   := embedX cc.code.n clb.basis.lx,
    lz   := embedZ cc.code.n clb.basis.lz,
    live := true, own := .owned }

/-- **The normal ChainQ → TypeChecker path**: elaborate and validate, packaging
    the `Block.valid` proof.  Errors (`malformedBlock`) only if the symplectic
    block fails to validate. -/
def toTypedBlock? (cc : CheckedCSSCode) (clb : CheckedLogicalBasis) : Except TypeError TypedBlock :=
  validateBlock? 0 (elaborateBlock cc clb)

/-- Convenience: derive the logical basis (via ChainQ) then elaborate to a
    `TypedBlock`. -/
def cssToTypedBlock? (cc : CheckedCSSCode) : Except TypeError TypedBlock :=
  match ChainQ.mkLogicalBasis cc with
  | .ok clb  => toTypedBlock? cc clb
  | .error _ => .error (.malformedBlock 0)

/-! ## Tests: the full checked pipeline ChainQ ⇒ TypedBlock. -/

-- a bare logical qubit: mkCSS ⇒ derive basis ⇒ elaborate ⇒ valid TypedBlock (= oneQ).
example : (match ChainQ.mkCSS { n := 1, hx := [], hz := [] } with
           | .ok cc => ok? (cssToTypedBlock? cc) | _ => false) = true := by decide
-- surface(2): the family constructor all the way to a validated symplectic block.
example : (match ChainQ.mkSurface 2 with
           | .ok cc => ok? (cssToTypedBlock? cc) | _ => false) = true := by decide

end TypeChecker
