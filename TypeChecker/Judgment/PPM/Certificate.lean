/-
  TypeChecker.Judgment.PPM.Certificate — the `TypedPPM` evidence structure.
-/
import TypeChecker.Capability.Defs
import PPM.Basic

namespace TypeChecker
open ChainQ.GF2

/-! ## The judgment. -/

/-- Evidence that a logical measurement is realizable. -/
structure TypedPPM where
  target      : PPM.MTarget
  kind        : CapKind
  mergedN     : Nat
  obligations : List String
  deriving Repr

end TypeChecker
