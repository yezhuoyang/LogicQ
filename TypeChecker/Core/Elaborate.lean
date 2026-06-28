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
import ChainQ.LogicalIndex

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

/-- Elaborate a checked user logical-index declaration into a raw symplectic
    `Block`.  The row order is exactly the user-declared logical indexing. -/
def elaborateIndexedBlock (idx : CheckedLogicalIndex) : Block :=
  { n    := idx.code.n,
    stab := cssToStab idx.code,
    lx   := embedX idx.code.n idx.basis.lx,
    lz   := embedZ idx.code.n idx.basis.lz,
    live := true, own := .owned }

/-- Validate the TypeChecker block obtained from a user-declared logical index. -/
def indexedToTypedBlock? (idx : CheckedLogicalIndex) : Except TypeError TypedBlock :=
  validateBlock? 0 (elaborateIndexedBlock idx)

/-- A typed block plus the source-level names for its logical-qubit rows. -/
structure TypedLogicalInterface where
  block : TypedBlock
  names : List String

private def logicalNameIndexOfAux (needle : String) : List String -> Nat -> Option Nat
  | [], _ => none
  | x :: xs, i => if x == needle then some i else logicalNameIndexOfAux needle xs (i + 1)

def TypedLogicalInterface.indexOf? (iface : TypedLogicalInterface) (name : String) : Option Nat :=
  logicalNameIndexOfAux name iface.names 0

/-- Strict ChainQ-to-TypeChecker bridge preserving user logical names. -/
def checkedIndexToTypedInterface? (idx : CheckedLogicalIndex) :
    Except TypeError TypedLogicalInterface := do
  let block ← indexedToTypedBlock? idx
  return { block, names := idx.names }

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
example : (match ChainQ.mkCSS ChainQ.bareQubit with
           | .ok cc =>
             match ChainQ.mkLogicalIndex? cc ChainQ.bareQubitIndexSpec with
             | .ok idx => ok? (checkedIndexToTypedInterface? idx)
             | .error _ => false
           | .error _ => false) = true := by decide
-- surface(2): the family constructor all the way to a validated symplectic block.
example : (match ChainQ.mkSurface 2 with
           | .ok cc => ok? (cssToTypedBlock? cc) | _ => false) = true := by decide

end TypeChecker
