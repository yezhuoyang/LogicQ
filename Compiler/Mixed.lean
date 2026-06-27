/-
  Compiler.Mixed — AGGREGATOR (M19 refactor) for the MIXED logical-execution IR.

  DESIGN SHIFT (M9): PPM is ONE checked target sublanguage, not the universal
  compiler target.  A logical program is a sequence of `MixedInstr`s in which
  native PPM/PPU fragments, TYPED transversal gates, arbitrary logical
  automorphisms, code switches, magic obligations, and logical Paulis coexist as
  FIRST-CLASS instructions.

  After M19 the IR is split into layer modules; this module re-exports the SYNTAX
  and CHECKER layers (every name is in `namespace Compiler`, so `import` re-exports
  transitively), preserving `import Compiler.Mixed` for existing users:
    * `Compiler.Mixed.Syntax` — `MagicKind`/`MagicObligation`/`MixedInstr`/`LogicalExec`/
      `isMagic`/`progNoMagic`/`LogicalOp`/`hGate2x2`/`sGate2x2`/`MixedInstr.action`/`singleLogicalBlock`
    * `Compiler.Mixed.Check`  — `checkInstr`/`checkLogicalExecAux`/`checkLogicalExec`
      (+ the legacy private cost-driven selector and its tests)

  (The SOURCE typing, the LOWERING, and the operational SEMANTICS live under
  `Compiler.MixedSemantics`, which re-exports `Compiler.Mixed.{Source,Lower,Semantics}`.)
-/
import Compiler.Mixed.Syntax
import Compiler.Mixed.Check
