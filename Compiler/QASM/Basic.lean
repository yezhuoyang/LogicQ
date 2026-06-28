/-
  Compiler.QASM — PUBLIC AGGREGATE (umbrella) for the QASM front-end.

  PUBLIC ENTRYPOINT: `import Compiler.QASM.Basic` for the QASM → LogicQ logical-qubit
  allocation layer.  `Syntax.lean` is the small OpenQASM-2-style source AST + contract
  boundary; `Allocate.lean` is the first-fit logical allocation + basis-tagged ancilla pool
  + typed MixIR emission (reusing the verified `Compiler.ChainQ2Mixed` compiler for all
  legality checking); `Parse.lean` is the total OpenQASM-2 text parser (text → AST) plus the
  `compileOpenQASM2ToMixIR?` parse+compile helper.  See `README.md` for the compatibility
  contract.  `AuditTests.lean` holds additive adversarial-audit regression tests.
-/
import Compiler.QASM.Syntax
import Compiler.QASM.Allocate
import Compiler.QASM.Parse
import Compiler.QASM.Physical
import Compiler.QASM.AuditTests

namespace Compiler.QASM

end Compiler.QASM
