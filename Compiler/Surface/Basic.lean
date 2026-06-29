/-
  Compiler.Surface — PUBLIC AGGREGATE (umbrella) for the LogicQ surface-language
  (`.lqr`) text front-end.

  PUBLIC ENTRYPOINT: `import Compiler.Surface.Basic`.  `Parse.lean` is the total `.lqr`
  text parser (human-readable surface text → the checked `Compiler.QASM` AST) plus
  `compileSurfaceToMixIR?`, which compiles a surface program end to end through the
  already-verified `Compiler.QASM.compileQASMToMixIR?` backend (no new lowering).  See
  `README.md` for the BNF grammar and the honest v0 scope (bare blocks; richer code
  families via the ChainQ `code … as …` macros).
-/
import Compiler.Surface.Parse

namespace Compiler.Surface

end Compiler.Surface
