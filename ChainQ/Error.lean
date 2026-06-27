/-
  ChainQ.Error — SHIM (M20 strict-folder-ownership refactor).
  The implementation now lives in `ChainQ.Core.Error`; this shim re-exports it
  (namespace unchanged) so `import ChainQ.Error` keeps resolving.
-/
import ChainQ.Core.Error
