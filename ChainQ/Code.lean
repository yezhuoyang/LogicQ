/-
  ChainQ.Code — SHIM (M20 strict-folder-ownership refactor).
  The implementation now lives in `ChainQ.Core.Code`; this shim re-exports it
  (namespace unchanged) so `import ChainQ.Code` keeps resolving.
-/
import ChainQ.Core.Code
