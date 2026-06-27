/-
  Compiler.Mixed.Lower — AGGREGATOR (M20 strict-folder-ownership refactor).

  The resource-aware compilation relation + the public compiler, split by ownership
  under Compiler/Mixed/Lower/ (dependency DAG: Op → {Program, LocMap} → {ProgramOk,
  Ancilla} → Public → Examples):
    * `Mixed.Lower.Op`        — `compileOpR` + soundness/completeness/action theorems
    * `Mixed.Lower.Program`   — `compileProgram` / `compileProgram_sound`
    * `Mixed.Lower.ProgramOk` — `Resources`/`progOpOk`/`ProgramOk`/`ProgramOkSupported`(+`_compiles`)
    * `Mixed.Lower.LocMap`    — `LocMap`/`LogicalOp.resolve`/`compileProgramLoc`(+`_sound`)
    * `Mixed.Lower.Ancilla`   — `AncillaSupply`/`AncillaPool`/`compileProgramLocA`(+`_sound`)
    * `Mixed.Lower.Public`    — `CompiledMixed`/`CompileMode`/`CompileConfig`/`compile?`/`sourceCompilable`
    * `Mixed.Lower.Examples`  — `tenvQ2` + the test examples

  Every name stays in `namespace Compiler`, so `import Compiler.Mixed.Lower` keeps
  resolving `compile?`/`compileOpR`/`CompiledMixed`/… unchanged.
-/
import Compiler.Mixed.Lower.Op
import Compiler.Mixed.Lower.Program
import Compiler.Mixed.Lower.ProgramOk
import Compiler.Mixed.Lower.LocMap
import Compiler.Mixed.Lower.Ancilla
import Compiler.Mixed.Lower.Public
import Compiler.Mixed.Lower.Examples
