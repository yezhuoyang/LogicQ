/-
  ChainQ.Checked — AGGREGATOR (M19 refactor).

  The TYPED CORE of the ChainQ front-end.  A well-formed code object CARRIES its
  validity proof (`CheckedCSSCode`, `CheckedLogicalBasis`); public constructors
  return `Except ChainQError _`.  After M19 the shared core and the per-family
  checked constructors live in:
    * `ChainQ.Checked.Basic`        — `CheckedCSSCode`, `CheckedLogicalBasis`, `isOk`,
                                      `mkCSS`, `mkLogicalBasis` (+ soundness theorems)
    * `ChainQ.Surface.Checked`      — `mkSurface`
    * `ChainQ.Toric.Checked`        — `mkToric`
    * `ChainQ.HGPCode.Checked`      — `mkHGP`
    * `ChainQ.BBCode.Checked`       — `mkBB`
    * `ChainQ.LiftedProduct.Checked`— `mkLiftedProduct`

  This module re-exports them all (every name is in `namespace ChainQ`), so
  existing users of `import ChainQ.Checked` keep resolving unchanged.
-/
import ChainQ.Checked.Basic
import ChainQ.HGPCode.Checked
import ChainQ.Surface.Checked
import ChainQ.Toric.Checked
import ChainQ.BBCode.Checked
import ChainQ.LiftedProduct.Checked
