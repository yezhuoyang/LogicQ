/-
  TypeChecker.Basic — PUBLIC AGGREGATE (umbrella) for the type checker (level L_TC).

  PUBLIC ENTRYPOINT: `import TypeChecker.Basic` for the whole checker layer.
  Root-level `.lean` files are intentionally FORBIDDEN (M21).  Internal modules live
  under `TypeChecker/Core/` (symplectic algebra, blocks, elaboration, errors),
  `TypeChecker/Capability/` (capability defs), `TypeChecker/Judgment/` (the per-judgment
  folders `Transversal/`, `Switch/`, `PPM/`, `PPMProgram/`), and `TypeChecker/Soundness.lean`.
-/
import TypeChecker.Core.Symplectic
import TypeChecker.Core.Error
import TypeChecker.Core.Block
import TypeChecker.Core.Elaborate
import TypeChecker.Capability.Defs
import TypeChecker.Judgment.Transversal
import TypeChecker.Judgment.Switch
import TypeChecker.Judgment.PPM
import TypeChecker.Judgment.PPMProgram
import TypeChecker.Soundness
