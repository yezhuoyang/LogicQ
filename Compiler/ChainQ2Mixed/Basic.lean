/-
  Compiler.ChainQ2Mixed — a thin, verified front-end + (forthcoming) path/schedule
  layer that compiles a ChainQ-typed logical program down to the existing Mixed IR.

  The Mixed IR already expresses all three realization paths (transversal /
  transversalCNOT / automorphism, ppm, switch); this layer adds the ChainQ-typed
  SOURCE (named code families + name-addressed ops) and will make the per-op PATH
  choice and the parallel SCHEDULE first-class and schedulable.  See the per-file
  docstrings and `README.md` for the honest scope.
-/
import Compiler.ChainQ2Mixed.Source
import Compiler.ChainQ2Mixed.Path
import Compiler.ChainQ2Mixed.Schedule
import Compiler.ChainQ2Mixed.Primitive
import Compiler.ChainQ2Mixed.Compile
import Compiler.ChainQ2Mixed.Frame

namespace Compiler.ChainQ2Mixed

end Compiler.ChainQ2Mixed
