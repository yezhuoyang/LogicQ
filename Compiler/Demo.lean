/-
  Compiler.Demo — AGGREGATOR (M19 refactor) for the demo-complete pipeline:

      Source program (LogicalOp)  →  compile?  →  Mixed IR  →  Simulator

  ONE source AST (`LogicalOp`) is used by BOTH the compiler and the simulator.
  After M19 the demo is split by topic (every name is in `namespace Compiler.Demo`,
  so `import` re-exports transitively):
    * `Compiler.Demo.Common`     — shared fixtures (`envN`/`tenv2`/`tenv4`/`demoCfg`/`dj2Cfg`/`famCfg`)
    * `Compiler.Demo.Direct`     — direct H;S;H pipeline (exact source = emitted)
    * `Compiler.Demo.Algorithms` — DJ/Grover/Simon source programs + ideal outcomes + `sourceCompilable`
    * `Compiler.Demo.Frames`     — operational `execMixed` tests (X/Z/H/DJ) + `exactSupportedOp` + negative syntax
    * `Compiler.Demo.Entangling` — typechecked CNOT lowering with an adapter capability (NOT channel-correct)
    * `Compiler.Demo.Families`   — surface/toric/HGP/BB/lifted-product compile-through

  ASSUMPTIONS (stated plainly — see Compiler/README.md for the lowering + exact/ideal/
  deferred tier tables): direct logical ops + a `.pauli` are EXACT operationally; PPM
  gadgets (`CNOT`/`CZ`/multi-logical `H`/`S`) are typechecked lowerings with an IDEAL
  gadget-channel assumption; there is NO distance / fault-tolerance proof; code-switch
  certificates are EXTERNAL/ASSUMED (`Compiler.CodeSwitch`).
-/
import Compiler.Demo.Common
import Compiler.Demo.Direct
import Compiler.Demo.Algorithms
import Compiler.Demo.Frames
import Compiler.Demo.Entangling
import Compiler.Demo.Families
import Compiler.Demo.Contract
