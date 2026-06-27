/-
  LogicQ.Basic — PUBLIC AGGREGATE: the FULL pipeline umbrella.

  PUBLIC ENTRYPOINT: `import LogicQ.Basic` to pull in every layer of the LogicQ
  verified-compilation pipeline (a "quantum CompCert"): the logical/physical
  vocabularies, the chain-complex front-end (ChainQ), the PPR / PPM / QStab / QClifford
  IRs, the type checker, and the inter-level compiler.

  Root-level `.lean` files are intentionally FORBIDDEN (M21 root-clean layout): each
  top-level folder owns exactly one public aggregate `<Folder>/Basic.lean`; everything
  else under a folder is an internal implementation module.
-/
import Logical.Basic
import Physical.Basic
import ChainQ.Basic
import PPR.Basic
import PPM.Basic
import QStab.Basic
import QClifford.Basic
import TypeChecker.Basic
import Compiler.Basic
