/-
  TypeChecker.Judgment.Switch.Cert — the switch protocol kind, the switch
  certificate, and the typed-switch evidence structures.
-/
import TypeChecker.Core.Block

namespace TypeChecker
open ChainQ ChainQ.GF2

/-- The physical protocol realizing a switch — selects the obligations, not the
    algebraic certificate (which is unified). -/
inductive SwitchKind
  | gaugeFix          -- gauging logical operators / subsystem gauge fixing (2410.02213)
  | transversalCNOT   -- one-way transversal CNOT switching (2409.13465)
  | dimensionJump     -- transversal dimension jump for product codes (2510.07269)
  | teleport          -- gate-teleportation bridge
  deriving DecidableEq, Repr

/-- A switch certificate: the protocol kind and the symplectic map `f` (a
    `2n_C × 2n_D` `BoolMat`) realizing the transparent coercion. -/
structure SwitchCert where
  kind : SwitchKind
  f    : BoolMat
  deriving Repr

/-- Evidence that a code switch is legal: the new code dimension, the induced
    (preserved) logical basis in D, and the deferred obligations. -/
structure TypedSwitch where
  block       : BlockId
  kind        : SwitchKind
  toN         : Nat
  inducedLX   : BoolMat
  inducedLZ   : BoolMat
  obligations : List String
  deriving Repr

end TypeChecker
