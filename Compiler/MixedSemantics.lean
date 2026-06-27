/-
  Compiler.MixedSemantics — AGGREGATOR (M19 refactor) for the PL theory of the mixed IR.

  Source typing judgments, a resource-aware compilation relation with soundness and
  (fragment) completeness, `compileProgram`/`compile?`, and ONE shared operational
  semantics (`ExecState`/`Step`) for all coexisting IR fragments.

  After M19 these are split into layer modules; this module re-exports them (every
  name is in `namespace Compiler`, so `import` re-exports transitively), preserving
  `import Compiler.MixedSemantics` for existing users (Simulator, Demo, Compiler.lean):
    * `Compiler.Mixed.Source`    — `srcOpOk`/`LogicalOp.srcAction`/`progOpNext`/`sourceOpOk`/`sourceWellFormed`
    * `Compiler.Mixed.Lower`     — `compileOpR`/`compileProgram*`/`ProgramOk*`/`LocMap*`/`Ancilla*`/
      `compileProgramLocA*`/`CompiledMixed`/`CompileMode`/`CompileConfig`/`compile?`/`sourceCompilable`
    * `Compiler.Mixed.Semantics` — `MixedInterp`/`ExecState`/`Step`/`Steps` + soundness/progress lemmas

  The DIRECT unitary fragment (transversal/automorphism) is realized EXACTLY at the
  symplectic level; a logical Pauli (`.pauli`) is APPLIED to the carrier; full
  PPM-gadget channel correctness is deferred.
-/
import Compiler.Mixed.Source
import Compiler.Mixed.Lower
import Compiler.Mixed.Semantics
