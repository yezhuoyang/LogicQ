/-
  ChainQ.GF2 — SHIM (M20 strict-folder-ownership refactor).
  The implementation now lives in `ChainQ.Algebra.GF2`; this shim re-exports it
  (namespace unchanged) so `import ChainQ.GF2` keeps resolving.
-/
import ChainQ.Algebra.GF2
