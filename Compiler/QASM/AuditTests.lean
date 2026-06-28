/-
  Compiler.QASM.AuditTests — adversarial-audit regression tests for the QASM → ChainQ
  logical-allocation → MixedIR path.

  These are ADDITIVE, SELF-CONTAINED `by decide` tests covering well-definedness / honest
  rejection corners that the main `Allocate.lean` / `Parse.lean` suites do not pin down:
  CRLF + header/include/comment text, ZERO-SIZE registers (accepted as vacuous, but any
  reference to them rejected), a MISSING `logicalIndex` (rejected by the ChainQ elaboration
  boundary), multi-`qreg` first-fit ordering, text-level "too few data logicals", a
  whole-register `barrier` on an UNKNOWN register (parse error), an out-of-range classical
  bit, and the STRICT-CNOT mode (a supplied incidence with `cnotMode := .strictTransversal`
  rejects an inapplicable transversal instead of falling back).

  Fixtures are defined INLINE over stable public types only (`ChainQ.NamedCodeDecl`,
  `AllocationRequest`, `NamedAnc`, `compileOpenQASM2ToMixIR?`), so this file does not couple
  to the test fixtures inside `Allocate.lean`.
-/
import Compiler.QASM.Parse

namespace Compiler.QASM.Audit

open Compiler.QASM Compiler.ChainQ2Mixed TypeChecker

-- text-parse `by decide` tests reduce structural recursion over the source char list.
set_option maxRecDepth 10000

/-! ## Inline fixtures (bare register codes; identity logical bases). -/

/-- A bare `n=3` register: 2 data logicals `d0`,`d1` + 1 ancilla logical `a0`. -/
def reg3 : ChainQ.NamedCodeDecl :=
  { name := "reg", decl := .css { n := 3, hx := [], hz := [] },
    logicalIndex := some
      { names := ["d0", "d1", "a0"],
        pauliBasis :=
          { zBasis    := [[true, false, false], [false, true, false], [false, false, true]],
            xDualBasis := [[true, false, false], [false, true, false], [false, false, true]] } } }

/-- One data logical (`d0`), no ancillas — enough for Pauli + readout on `d0`. -/
def req1 : AllocationRequest :=
  { decls := [reg3], dataLogicals := [⟨"reg", "d0"⟩], ancillas := [] }

/-- Two data logicals (`d0`,`d1`) + a `|+⟩` ancilla (`a0`) — enough for an intra-block CX gadget. -/
def reqCX : AllocationRequest :=
  { decls := [reg3], dataLogicals := [⟨"reg", "d0"⟩, ⟨"reg", "d1"⟩],
    ancillas := [{ code := "reg", logical := "a0", basis := .plus }] }

/-- The empty request (no codes, no data) — for vacuous programs over zero-size registers. -/
def reqEmpty : AllocationRequest := { decls := [], dataLogicals := [], ancillas := [] }

/-- A declaration MISSING its `logicalIndex` — the ChainQ elaboration boundary must reject it. -/
def noIdxDecl : ChainQ.NamedCodeDecl :=
  { name := "ni", decl := .css { n := 1, hx := [], hz := [] }, logicalIndex := none }
def reqNoIdx : AllocationRequest :=
  { decls := [noIdxDecl], dataLogicals := [⟨"ni", "data"⟩], ancillas := [] }

/-! ## §1. Text robustness — CRLF, header, include, comments together. -/

-- a Windows-CRLF program with header / include / comment / qreg / creg / x / measure compiles:
example : ok? (compileOpenQASM2ToMixIR? []
    "OPENQASM 2.0;\r\ninclude \"qelib1.inc\";\r\nqreg q[1];\r\ncreg c[1];\r\nx q[0]; // readout\r\nmeasure q[0] -> c[0];\r\n"
    req1) = true := by decide

-- CRLF parses to exactly the intended AST (no stray `\r` leaks into names):
example : (match parseOpenQASM2? "qreg q[1];\r\nx q[0];\r\n" with
    | .ok p    => decide (p = { qregs := [⟨"q", 1⟩], cregs := [], instrs := [.x ⟨"q", 0⟩] })
    | .error _ => false) = true := by decide

/-! ## §2. Zero-size registers — accepted as VACUOUS, but any reference rejected. -/

-- `qreg q[0]; creg c[0];` declares no addressable qubit/bit: a vacuous program compiles:
example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[0]; creg c[0];" reqEmpty) = true := by decide
-- referencing a zero-size register's qubit is rejected (no silent mis-compilation):
example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[0]; x q[0];" reqEmpty) = false := by decide
-- a zero-size qreg contributes no virtual qubits to the first-fit flatten:
example : (match parseOpenQASM2? "qreg q[0];" with
    | .ok p    => decide (p.flatQubits = [])
    | .error _ => false) = true := by decide

/-! ## §3. ChainQ legality boundary — a missing `logicalIndex` is rejected. -/

-- `noIdxDecl` has `logicalIndex := none`; `mkAddrCtx?`/`elabDecls?`/`checkLogicalIndex?` reject it:
example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[1]; x q[0];" reqNoIdx) = false := by decide

/-! ## §4. First-fit over MULTIPLE qregs — stable declaration order. -/

-- two qregs flatten in declaration order (q before r):
example : (match parseOpenQASM2? "qreg q[1]; qreg r[1];" with
    | .ok p    => decide (p.flatQubits = [⟨"q", 0⟩, ⟨"r", 0⟩])
    | .error _ => false) = true := by decide
-- and end-to-end: `q`→`d0`, `r`→`d1` (first-fit), so `cx q[0],r[0]` is the intra-block CX:
example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[1]; qreg r[1]; cx q[0],r[0];" reqCX) = true := by decide

/-! ## §5. Text-level resource shortfall — `qreg q[3]` with only two data logicals. -/

example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[3]; x q[0];" reqCX) = false := by decide

/-! ## §6. Honest rejection corners — bad barrier register, bad classical bit. -/

-- a whole-register `barrier` on an UNDECLARED register is a PARSE error (it cannot expand):
example : (match parseOpenQASM2? "qreg q[1]; barrier r;" with | .error _ => true | .ok _ => false) = true := by decide
example : (match compileOpenQASM2ToMixIR? [] "qreg q[1]; barrier r;" req1 with
    | .error (.parse _) => true | _ => false) = true := by decide
-- a barrier on a DECLARED register expands and compiles (it is then dropped during lowering):
example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[1]; barrier q; x q[0];" req1) = true := by decide
-- a measurement into an out-of-range classical bit is rejected:
example : ok? (compileOpenQASM2ToMixIR? []
    "qreg q[1]; creg c[1]; measure q[0] -> c[99];" req1) = false := by decide

/-! ## §7. Strict CNOT — a supplied incidence that is INAPPLICABLE rejects (no PPM fallback).

    NOTE on the contract: the QASM `cnotMode` default is `preferTransversalWithPPMFallback`,
    so a bare `cnotIncidence` alone SILENTLY FALLS BACK to the PPM gadget for an intra-block
    `cx` (see `Allocate.lean`'s test 488).  The mission's "strict" semantics are obtained by
    setting `cnotMode := .strictTransversal`, which is what this test pins down: the same
    intra-block `cx` is then REJECTED rather than silently downgraded. -/
example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[2]; cx q[0],q[1];"
    { reqCX with cnotMode := .strictTransversal, cnotIncidence := some [[true]] }) = false := by decide
-- a malformed program is a PARSE error, distinct from the compile phase:
example : (match compileOpenQASM2ToMixIR? [] "qreg q[1" req1 with
    | .error (.parse _) => true | _ => false) = true := by decide

end Compiler.QASM.Audit
