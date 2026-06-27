/-
  Compiler.CodeSwitch — SHIM (M20 strict-folder-ownership refactor).

  The typed code-switch / dimension-jump certificate skeleton (EXTERNAL/ASSUMED, not
  verification) now lives in `Compiler.CodeSwitch.Basic`; this shim re-exports it
  (namespace `Compiler.CodeSwitch` unchanged) so `import Compiler.CodeSwitch` keeps
  resolving `SwitchProtocolCert`/`structuralCheck`/… unchanged.
-/
import Compiler.CodeSwitch.Basic
