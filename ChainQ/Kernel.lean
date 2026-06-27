/-
  ChainQ.Kernel — SHIM (M20 strict-folder-ownership refactor).
  The implementation now lives in `ChainQ.Algebra.Kernel`; this shim re-exports it
  (namespace unchanged) so `import ChainQ.Kernel` keeps resolving.
-/
import ChainQ.Algebra.Kernel
