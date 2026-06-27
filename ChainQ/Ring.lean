/-
  ChainQ.Ring — SHIM (M20 strict-folder-ownership refactor).
  The implementation now lives in `ChainQ.Algebra.Ring`; this shim re-exports it
  (namespace unchanged) so `import ChainQ.Ring` keeps resolving.
-/
import ChainQ.Algebra.Ring
