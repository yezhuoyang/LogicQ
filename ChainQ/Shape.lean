/-
  ChainQ.Shape — SHIM (M20 strict-folder-ownership refactor).
  The implementation now lives in `ChainQ.Algebra.Shape`; this shim re-exports it
  (namespace unchanged) so `import ChainQ.Shape` keeps resolving.
-/
import ChainQ.Algebra.Shape
