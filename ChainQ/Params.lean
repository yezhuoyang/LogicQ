/-
  ChainQ.Params — SHIM (M20 strict-folder-ownership refactor).
  The implementation now lives in `ChainQ.Core.Params`; this shim re-exports it
  (namespace unchanged) so `import ChainQ.Params` keeps resolving.
-/
import ChainQ.Core.Params
