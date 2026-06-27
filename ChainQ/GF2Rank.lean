/-
  ChainQ.GF2Rank — SHIM (M20 strict-folder-ownership refactor).
  The implementation now lives in `ChainQ.Algebra.GF2Rank`; this shim re-exports it
  (namespace unchanged) so `import ChainQ.GF2Rank` keeps resolving.
-/
import ChainQ.Algebra.GF2Rank
