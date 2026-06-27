/-
  ChainQ.Families — AGGREGATOR (M19 refactor).

  The parametric QEC code-family constructors now live in per-family folders:
    * `ChainQ.HGPCode.Repetition` — `repOpen`, `repCyc`
    * `ChainQ.HGPCode.Basic`      — `Internal.hgp`, `hgp?`
    * `ChainQ.Surface.Basic`      — `surface`, `surface?`
    * `ChainQ.Toric.Basic`        — `toric`, `toric?`
    * `ChainQ.BBCode.Basic`       — `Internal.bb`, `bb?`
    * `ChainQ.LiftedProduct.Basic`— `Internal.liftedProduct`, `liftedProduct?`

  This module re-exports them all (every name is in `namespace ChainQ` /
  `ChainQ.Internal`, so `import` re-exports transitively) so existing users of
  `import ChainQ.Families` keep resolving unchanged.  Sources:
    * HGP / surface / toric — Tillich–Zémor, arXiv 0903.0566.
    * lifted product       — Panteleev–Kalachev, arXiv 2012.04068.
    * bivariate bicycle    — arXiv 2410.03628.
-/
import ChainQ.HGPCode.Repetition
import ChainQ.HGPCode.Basic
import ChainQ.Surface.Basic
import ChainQ.Toric.Basic
import ChainQ.BBCode.Basic
import ChainQ.LiftedProduct.Basic

namespace ChainQ
open ChainQ.GF2

/-! ## CSS-condition NEGATIVE tests (kept here — they use only `ChainQ.Code`). -/

example : ({ n := 2, hx := [[true, true]], hz := [[true, false]] } : CSSCode).cssCondition = false := by decide  -- anticommuting checks
example : ({ n := 3, hx := [[true, true]], hz := [[true, false, true]] } : CSSCode).wellShaped = false := by decide  -- ragged hx (len 2 ≠ n=3)

end ChainQ
