/-
  Compiler.LogicalToPPM — SHIM (M19 refactor).

  The PPM-FRAGMENT proof-carrying evidence (`CompiledPPM`) moved to the intended
  pipeline-stage folder `Compiler/PPR2PPM/Basic.lean` (module `Compiler.PPR2PPM.Basic`).
  This shim re-exports it (same `namespace Compiler`) so existing
  `import Compiler.LogicalToPPM` users keep resolving unchanged.
-/
import Compiler.PPR2PPM.Basic
