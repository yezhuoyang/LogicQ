/-
  Compiler.LogicalToQStab — SHIM (M19 refactor).

  The PPM→QStab lattice-surgery bridge + surgery certificate moved to the intended
  pipeline-stage folder `Compiler/LS2QStab/Basic.lean` (module `Compiler.LS2QStab.Basic`).
  This shim re-exports it (same `namespace Compiler`) so existing
  `import Compiler.LogicalToQStab` users keep resolving unchanged.
-/
import Compiler.LS2QStab.Basic
