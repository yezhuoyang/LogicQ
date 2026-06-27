/-
  ChainQ.ChainComplex — SHIM (M20 strict-folder-ownership refactor).
  The implementation now lives in `ChainQ.Core.ChainComplex`; this shim re-exports it
  (namespace unchanged) so `import ChainQ.ChainComplex` keeps resolving.
-/
import ChainQ.Core.ChainComplex
