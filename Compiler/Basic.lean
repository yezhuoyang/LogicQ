/-
  Compiler.Basic — PUBLIC AGGREGATE (umbrella) for the inter-level compiler passes.

  PUBLIC ENTRYPOINT: `import Compiler.Basic` for the whole compiler layer.
  Root-level `.lean` files are intentionally FORBIDDEN (M21).  Internal modules live
  under `Compiler/Mixed/` (the Mixed IR + checker + source typing + lowering +
  semantics), `Compiler/Simulator/` (the exact GInt simulator + `execMixed`),
  `Compiler/ChainQ2Mixed/` and `Compiler/QASM/` (ChainQ/QASM-facing logical
  allocation into checked Mixed IR), `Compiler/Surface/` (the `.lqr` surface-language
  text front-end, compiling through the QASM backend),
  `Compiler/PPR2PPM/`, `Compiler/LS2QStab/`, and `Compiler/QStab2QClifford/`
  (pass-stage bridges),
  `Compiler/CodeSwitch/` (external/assumed code-switch certificates), and
  `Compiler/Demo/` (the demo-complete pipeline).  `LogicalToPPM`/`LogicalToQStab` are
  thin compatibility shims for the pass-stage modules.
-/
import Compiler.LogicalToPPM
import Compiler.Mixed
import Compiler.MixedSemantics
import Compiler.Simulator
import Compiler.LogicalToQStab
import Compiler.ChainQ2Mixed.Basic
import Compiler.QASM.Basic
import Compiler.Surface.Basic
import Compiler.QStab2QClifford.Basic
import Compiler.CodeSwitch
import Compiler.Verification.Basic
import Compiler.Verification.Compile
import Compiler.Demo
