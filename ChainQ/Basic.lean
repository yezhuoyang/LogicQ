/-
  ChainQ.Basic — PUBLIC AGGREGATE (umbrella) for the ChainQ front-end (level L_FE).

  PUBLIC ENTRYPOINT: `import ChainQ.Basic` to pull in the whole ChainQ layer.
  Root-level `.lean` files are intentionally FORBIDDEN (M21) — every top-level layer
  is imported through its folder-owned `<Folder>/Basic.lean`.  Internal implementation
  modules live under `ChainQ/Algebra/` (GF(2) / circulant-ring algebra), `ChainQ/Core/`
  (code types + chain complexes + params/errors), the per-family folders
  (`HGPCode/Surface/Toric/BBCode/LiftedProduct/`), `ChainQ/Checked/`, and
  `ChainQ/Materialize/` (the CSS → concrete check / stabilizer matrix API).
-/
import ChainQ.GF2
import ChainQ.GF2Rank
import ChainQ.Shape
import ChainQ.Kernel
import ChainQ.Ring
import ChainQ.Code
import ChainQ.ChainComplex
import ChainQ.Materialize.Basic
import ChainQ.Families
import ChainQ.Params
import ChainQ.Distance
import ChainQ.Error
import ChainQ.Checked
import ChainQ.LogicalIndex
import ChainQ.Syntax
import ChainQ.Materialize.Tests
