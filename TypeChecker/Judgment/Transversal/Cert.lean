/-
  TypeChecker.Judgment.Transversal.Cert — the typed-automorphism and
  typed-transversal evidence structures.
-/
import TypeChecker.Core.Block

namespace TypeChecker
open ChainQ ChainQ.GF2

/-- Evidence that a symplectic map is a legal LOGICAL AUTOMORPHISM of a block:
    the verified `2n×2n` action and the induced logical map.  (This is what the
    original `checkTransversal` actually verified — an *arbitrary* code
    automorphism, not necessarily a local/tensor gate.) -/
structure TypedAutomorphism where
  block     : BlockId
  map       : BoolMat        -- the verified 2n×2n symplectic action
  inducedLX : BoolMat        -- M · lx  (induced action on logical X̄)
  inducedLZ : BoolMat        -- M · lz
  deriving Repr

/-- Evidence that a genuine TRANSVERSAL gate is legal: the local single-qubit
    gate, its tensor-power action, and the induced logical map. -/
structure TypedTransversal where
  block     : BlockId
  gate      : BoolMat        -- the verified 2×2 single-qubit symplectic
  map       : BoolMat        -- its tensor power = the verified 2n×2n action
  inducedLX : BoolMat
  inducedLZ : BoolMat
  deriving Repr

end TypeChecker
