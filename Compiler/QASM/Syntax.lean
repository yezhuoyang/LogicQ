/-
  Compiler.QASM.Syntax — a small OpenQASM-2-style SOURCE AST for the LogicQ
  front-end.

  This is the COMPATIBILITY-CONTRACT boundary (see `Compiler/QASM/README.md`): a
  deliberately small subset of OpenQASM 2 that LogicQ's logical gate/resource
  contract can currently realize — `qreg`/`creg` declarations and the
  `h s x z t cx cz measure barrier` instructions.  Anything outside that subset
  (arbitrary rotations `rx/rz/u3`, `reset`, dynamic `if`, custom gates) is modelled
  by the single `unsupported` constructor so the allocator can REJECT it as a
  correct compiler result ("not compatible with the current LogicQ contract"),
  rather than the parser silently dropping it.

  We start from an AST, NOT a text parser: a faithful text parser can be layered on
  top once the logical-allocation logic (`Compiler/QASM/Allocate.lean`) is stable.
  This module is pure data + Bool predicates — it has NO LogicQ dependency, so the
  contract surface stays auditable in isolation.
-/

namespace Compiler.QASM

/-! ## §1. Virtual qubit / classical-bit references. -/

/-- A VIRTUAL qubit: the `idx`-th qubit of a declared `qreg` named `reg`
    (`qreg reg[size]; … reg[idx]`).  "Virtual" = a SOURCE-program qubit, not yet
    mapped to a LogicQ logical qubit (that is the allocator's job). -/
structure VQubit where
  reg : String
  idx : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A VIRTUAL classical bit: the `idx`-th bit of a declared `creg` named `reg`. -/
structure VCBit where
  reg : String
  idx : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## §2. Register declarations. -/

/-- A quantum register declaration `qreg name[size];`. -/
structure QReg where
  name : String
  size : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A classical register declaration `creg name[size];`. -/
structure CReg where
  name : String
  size : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## §3. The supported instruction subset. -/

/-- A QASM instruction.  The first nine constructors are the SUPPORTED contract
    subset; `unsupported` is a parsed-but-rejected gate (arbitrary rotation,
    `reset`, custom gate, …) carrying only its source name for diagnostics. -/
inductive Instr where
  | h          (q : VQubit)
  | s          (q : VQubit)
  | x          (q : VQubit)
  | z          (q : VQubit)
  | t          (q : VQubit)
  | cx         (c t : VQubit)
  | cz         (c t : VQubit)
  | measure    (q : VQubit) (target : VCBit)
  | barrier    (qs : List VQubit)
  | unsupported (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- Is this a `barrier`?  Barriers carry no logical operation — they are dropped
    during lowering and do NOT count toward the generated-op total. -/
def Instr.isBarrier : Instr → Bool
  | .barrier _ => true
  | _          => false

/-- Is this an `unsupported` (out-of-contract) instruction? -/
def Instr.isUnsupported : Instr → Bool
  | .unsupported _ => true
  | _              => false

/-- The virtual qubits an instruction reads/writes (for reference validation). -/
def Instr.qubitRefs : Instr → List VQubit
  | .h q          => [q]
  | .s q          => [q]
  | .x q          => [q]
  | .z q          => [q]
  | .t q          => [q]
  | .cx c tgt     => [c, tgt]
  | .cz c tgt     => [c, tgt]
  | .measure q _  => [q]
  | .barrier qs   => qs
  | .unsupported _ => []

/-- The virtual classical bits an instruction writes (only `measure`). -/
def Instr.cbitRefs : Instr → List VCBit
  | .measure _ c => [c]
  | _            => []

/-! ## §4. Programs. -/

/-- A QASM program: quantum + classical register declarations and a list of
    instructions (in source order). -/
structure QASMProgram where
  qregs  : List QReg
  cregs  : List CReg
  instrs : List Instr
  deriving Repr, Inhabited

/-- Flatten the quantum registers, in declaration order, to the full list of
    virtual qubits `reg[0], reg[1], …`.  This ORDER fixes the first-fit logical
    allocation in `Compiler/QASM/Allocate.lean`. -/
def QASMProgram.flatQubits (p : QASMProgram) : List VQubit :=
  p.qregs.flatMap (fun r => (List.range r.size).map (fun i => ⟨r.name, i⟩))

/-- Flatten the classical registers, in declaration order. -/
def QASMProgram.flatCbits (p : QASMProgram) : List VCBit :=
  p.cregs.flatMap (fun r => (List.range r.size).map (fun i => ⟨r.name, i⟩))

/-- The first duplicated string in a list, if any. -/
def firstDuplicateString? : List String -> Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDuplicateString? xs

/-- The first duplicated `qreg` name, if any.  QASM register identifiers are unique
    inside their namespace; without this guard, two `qreg q[...]` declarations would
    flatten to the same virtual reference and make first-fit allocation ambiguous. -/
def QASMProgram.firstDuplicateQReg? (p : QASMProgram) : Option String :=
  firstDuplicateString? (p.qregs.map (·.name))

/-- The first duplicated `creg` name, if any. -/
def QASMProgram.firstDuplicateCReg? (p : QASMProgram) : Option String :=
  firstDuplicateString? (p.cregs.map (·.name))

/-- How many MixIR-bound logical operations the instructions generate: one per
    instruction EXCEPT barriers (which are dropped).  `unsupported` instructions
    are counted here but the allocator rejects the program before emission. -/
def QASMProgram.opCount (p : QASMProgram) : Nat :=
  (p.instrs.filter (fun i => ! i.isBarrier)).length

/-- Does a `qreg` declare this virtual qubit (name matches and index in range)? -/
def QASMProgram.declaresQ (p : QASMProgram) (q : VQubit) : Bool :=
  p.qregs.any (fun r => r.name == q.reg && decide (q.idx < r.size))

/-- Does a `creg` declare this virtual classical bit? -/
def QASMProgram.declaresC (p : QASMProgram) (c : VCBit) : Bool :=
  p.cregs.any (fun r => r.name == c.reg && decide (c.idx < r.size))

/-! ## §5. Smoke tests (pure-data level). -/

/-- A 2-qubit / 2-bit Bell-style fixture: `qreg q[2]; creg c[2]; h q[0]; cx q[0],q[1];`. -/
def bellProgram : QASMProgram :=
  { qregs := [⟨"q", 2⟩], cregs := [⟨"c", 2⟩],
    instrs := [.h ⟨"q", 0⟩, .cx ⟨"q", 0⟩ ⟨"q", 1⟩,
               .measure ⟨"q", 0⟩ ⟨"c", 0⟩, .measure ⟨"q", 1⟩ ⟨"c", 1⟩] }

example : bellProgram.flatQubits = [⟨"q", 0⟩, ⟨"q", 1⟩] := by decide
example : bellProgram.flatCbits = [⟨"c", 0⟩, ⟨"c", 1⟩] := by decide
example : bellProgram.firstDuplicateQReg? = none := by decide
example : bellProgram.firstDuplicateCReg? = none := by decide
example :
    ({ bellProgram with qregs := [⟨"q", 1⟩, ⟨"q", 2⟩] }).firstDuplicateQReg? =
      some "q" := by decide
example :
    ({ bellProgram with cregs := [⟨"c", 1⟩, ⟨"c", 2⟩] }).firstDuplicateCReg? =
      some "c" := by decide
example : bellProgram.opCount = 4 := by decide
example : bellProgram.declaresQ ⟨"q", 1⟩ = true := by decide
example : bellProgram.declaresQ ⟨"q", 2⟩ = false := by decide
example : bellProgram.declaresQ ⟨"r", 0⟩ = false := by decide
example : bellProgram.declaresC ⟨"c", 0⟩ = true := by decide
example : bellProgram.declaresC ⟨"c", 9⟩ = false := by decide
-- barriers are dropped from the op count:
example : ({ bellProgram with instrs := bellProgram.instrs ++ [Instr.barrier [⟨"q", 0⟩]] }).opCount = 4 := by decide

end Compiler.QASM
