/-
  Compiler.Simulator — AGGREGATOR (M20 strict-folder-ownership refactor).

  An EXACT ideal Gaussian-integer logical simulator + the `Step`-aligned executable
  interpreter, split by ownership under Compiler/Simulator/ (DAG: Arithmetic → State →
  Gate → {Algorithms, ExecMixed} → Examples):
    * `Simulator.Arithmetic` — `GInt` (a+bi over ℤ) + its ops/instances
    * `Simulator.State`      — `State`/`bit`/`flipBit`/`amp`/`init`
    * `Simulator.Gate`       — `Gate`/`applyGate`/`runGates`/`regProb`
    * `Simulator.Algorithms` — DJ / Grover / Simon gate fixtures
    * `Simulator.ExecMixed`  — `Layout`/`opGate?`/`sourceGates`/`mixedInstrToGate?`/`loweredGates`/
                               `simInterp`/`execInstr`/`execMixed`/`step_pauli_matches_exec`/`hshProg`
    * `Simulator.Examples`   — the algorithm-outcome / source-vs-emitted / PPM-channel tests

  Every name stays in `namespace Compiler.Sim`, so `import Compiler.Simulator` keeps
  resolving `runGates`/`execMixed`/`init`/… unchanged.
-/
import Compiler.Simulator.Arithmetic
import Compiler.Simulator.State
import Compiler.Simulator.Gate
import Compiler.Simulator.Algorithms
import Compiler.Simulator.ExecMixed
import Compiler.Simulator.Examples
