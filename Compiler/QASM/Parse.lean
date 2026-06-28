/-
  Compiler.QASM.Parse — a small, TOTAL OpenQASM-2 text parser for the LogicQ
  compatibility subset, layered on top of the checked `Compiler.QASM` AST.

  HONEST SCOPE.  This is text → `QASMProgram` (the AST in `Syntax.lean`) ONLY — it does
  NO logical allocation and NO legality checking (those stay in `Allocate.lean` /
  `compileChainQToMixIR?`).  The accepted grammar is deliberately tiny:

    OPENQASM 2.0;                     -- optional header, ignored
    include "qelib1.inc";             -- optional include, ignored (gates are modelled natively)
    // line comments                  -- stripped (a `;` inside a comment does NOT end a statement)
    qreg name[n];   creg name[n];
    h q[i];  s q[i];  sdg q[i];  x q[i];  z q[i];  t q[i];  tdg q[i];
    cx q[i],q[j];   cz q[i],q[j];
    measure q[i] -> c[j];
    barrier q[i];   barrier q[i],q[j],...;   barrier q;   -- `barrier q` = all qubits of register q

  Any OTHER gate-shaped statement (`rx(θ) q[0]`, `u3(...)`, `reset q[0]`, `if (...) ...`,
  `ccx ...`, a custom gate, …) parses to `Instr.unsupported <name>` — it is NEVER silently
  dropped; the allocator then rejects it as a correct "not compatible" result.  A
  statement that is not even gate-shaped (does not start with an identifier, has a
  malformed `[index]`, a non-numeric index, …) is a `ParseError`.  NO custom-gate
  expansion, NO rotation synthesis, NO `reset`, NO dynamic `if`.

  DECIDABILITY NOTE.  The whole parser is written over `List Char` (via `src.toList`) with
  structural recursion, and builds names with `String.ofList`, because the kernel does NOT
  reduce the `String.Pos`/`ByteArray`-based ops (`splitOn`/`trim`/`startsWith`/`toNat?`)
  used by a naive string parser — but it DOES reduce `"…".toList`, `Char` predicates, and
  `String.ofList` equality.  This keeps every parser test `by decide`-checkable.
-/
import Compiler.QASM.Allocate

namespace Compiler.QASM

open TypeChecker

-- The `by decide` parser tests reduce structural recursion over the source character list,
-- so they need more than the default elaborator recursion depth (512) for longer inputs.
set_option maxRecDepth 10000

/-! ## §1. Parse errors. -/

/-- A parse-phase error (distinct from the allocation/lowering `QASMError`). -/
inductive ParseError where
  | malformed        (msg : String)   -- a recognized statement with a malformed body
  | badInt           (lexeme : String) -- a register size / qubit index that is not a Nat
  | unknownStatement (text : String)  -- a statement that is not even gate-shaped
  deriving Repr, DecidableEq

/-! ## §2. Character-list lexing helpers (kernel-reducible, no `String.Pos`). -/

/-- ASCII whitespace. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- An identifier character (we require identifiers to START with a letter). -/
def isIdentChar (c : Char) : Bool := c.isAlpha || c.isDigit || c == '_'

/-- Drop leading whitespace. -/
def dropWs : List Char → List Char
  | c :: cs => if isWs c then dropWs cs else c :: cs
  | []      => []

/-- Trim leading + trailing whitespace from a char list. -/
def trimL (cs : List Char) : List Char := (dropWs (dropWs cs).reverse).reverse

/-- The leading run of identifier characters. -/
def takeIdent : List Char → List Char
  | c :: cs => if isIdentChar c then c :: takeIdent cs else []
  | []      => []

/-- Everything after the leading run of identifier characters. -/
def dropIdent : List Char → List Char
  | c :: cs => if isIdentChar c then dropIdent cs else c :: cs
  | []      => []

/-- The decimal value of a digit character, if it is one. -/
def digitVal? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat) else none

/-- Parse a NON-EMPTY all-digits char list to a `Nat` (no `String.toNat?`, which the
    kernel will not reduce). -/
def natOfDigitsAux : Nat → List Char → Option Nat
  | acc, []      => some acc
  | acc, c :: cs => match digitVal? c with
                    | some d => natOfDigitsAux (acc * 10 + d) cs
                    | none   => none

def natOfDigits? : List Char → Option Nat
  | [] => none
  | cs => natOfDigitsAux 0 cs

/-- Split a char list at the FIRST occurrence of `close`, returning `(before, after)`;
    `none` if `close` never appears. -/
def spanUntil (close : Char) : List Char → Option (List Char × List Char)
  | c :: cs => if c == close then some ([], cs)
               else match spanUntil close cs with
                    | some (a, b) => some (c :: a, b)
                    | none        => none
  | []      => none

/-- Split a char list at the FIRST `->`, returning `(before, after)`. -/
def spanArrow : List Char → Option (List Char × List Char)
  | '-' :: '>' :: cs => some ([], cs)
  | c :: cs => match spanArrow cs with
               | some (a, b) => some (c :: a, b)
               | none        => none
  | []      => none

/-- Split a char list on every occurrence of `sep` (always returns ≥ 1 segment).
    Tail-recursive so large normalized QASM files do not overflow the Lean interpreter. -/
def splitOnChar (sep : Char) (xs : List Char) : List (List Char) :=
  let rec go (cur : List Char) (acc : List (List Char)) : List Char → List (List Char)
    | [] => (cur.reverse :: acc).reverse
    | c :: cs =>
        if c == sep then go [] (cur.reverse :: acc) cs
        else go (c :: cur) acc cs
  go [] [] xs

/-- Strip `// … (end of line)` line comments.  The `Bool` is "currently inside a comment".
    Stripping happens BEFORE the `;` split, so a `;` inside a comment never ends a statement.
    Tail-recursive so large normalized QASM files do not overflow the Lean interpreter. -/
def stripComments (inside0 : Bool) (xs : List Char) : List Char :=
  let rec go (inside : Bool) (acc : List Char) : List Char → List Char
    | [] => acc.reverse
    | '\n' :: cs =>
        if inside then go false ('\n' :: acc) cs
        else go false ('\n' :: acc) cs
    | '/' :: '/' :: cs =>
        if inside then go true acc cs
        else go true acc cs
    | c :: cs =>
        if inside then go true acc cs
        else go false (c :: acc) cs
  go inside0 [] xs

/-! ## §3. Operand + statement parsers. -/

/-- Parse a single indexed reference `name[idx]` (whitespace-tolerant). -/
def parseIndexed (cs0 : List Char) : Except ParseError (String × Nat) :=
  let cs   := trimL cs0
  let name := takeIdent cs
  let rest := trimL (dropIdent cs)
  match name with
  | [] => .error (.malformed "expected a register name")
  | _  =>
    match rest with
    | '[' :: rest2 =>
        match spanUntil ']' rest2 with
        | some (content, after) =>
            if (trimL after).isEmpty then
              match natOfDigits? (trimL content) with
              | some n => .ok (String.ofList name, n)
              | none   => .error (.badInt (String.ofList (trimL content)))
            else .error (.malformed "trailing characters after ']'")
        | none => .error (.malformed "missing ']' in index")
    | _ => .error (.malformed "expected '[index]' after register name")

/-- Add an instruction to the program-in-progress.

    During parsing, `prog.instrs` is an internal reversed accumulator; `parseOpenQASM2?`
    restores source order exactly once at the public boundary. -/
def addInstr (prog : QASMProgram) (i : Instr) : QASMProgram :=
  { prog with instrs := i :: prog.instrs }

/-- Parse a one-qubit gate body `q[i]`. -/
def parse1Q (mk : VQubit → Instr) (prog : QASMProgram) (rest : List Char) :
    Except ParseError QASMProgram := do
  let (nm, i) ← parseIndexed rest
  .ok (addInstr prog (mk ⟨nm, i⟩))

/-- Parse a two-qubit gate body `q[i],q[j]`. -/
def parse2Q (mk : VQubit → VQubit → Instr) (prog : QASMProgram) (rest : List Char) :
    Except ParseError QASMProgram :=
  match splitOnChar ',' rest with
  | [a, b] => do
      let (n1, i1) ← parseIndexed a
      let (n2, i2) ← parseIndexed b
      .ok (addInstr prog (mk ⟨n1, i1⟩ ⟨n2, i2⟩))
  | _ => .error (.malformed "expected exactly two comma-separated qubits")

/-- Parse one qubit and append several primitive instructions.  Used for exact aliases
    such as `tdg`, so the allocator sees the expanded operation count. -/
def parse1QExpand (mk : VQubit → List Instr) (prog : QASMProgram) (rest : List Char) :
    Except ParseError QASMProgram := do
  let (nm, i) ← parseIndexed rest
  .ok { prog with instrs := (mk ⟨nm, i⟩).reverse ++ prog.instrs }

/-- Parse a `measure q[i] -> c[j]` body. -/
def parseMeasureStmt (prog : QASMProgram) (rest : List Char) :
    Except ParseError QASMProgram :=
  match spanArrow rest with
  | some (lhs, rhs) => do
      let (qn, qi) ← parseIndexed lhs
      let (cn, ci) ← parseIndexed rhs
      .ok (addInstr prog (.measure ⟨qn, qi⟩ ⟨cn, ci⟩))
  | none => .error (.malformed "expected 'measure q[i] -> c[j]'")

/-- Parse one `barrier` operand: either `q[i]` (one qubit) or `q` (all qubits of the
    already-declared register `q`). -/
def parseBarrierOp (prog : QASMProgram) (op : List Char) :
    Except ParseError (List VQubit) :=
  let s    := trimL op
  let name := takeIdent s
  match name with
  | [] => .error (.malformed "expected a register or qubit in 'barrier'")
  | _  =>
    match trimL (dropIdent s) with
    | [] =>                                   -- whole-register form `barrier q`
        let nm := String.ofList name
        match prog.qregs.find? (fun r => r.name == nm) with
        | some r => .ok ((List.range r.size).map (fun i => ⟨nm, i⟩))
        | none   => .error (.malformed "'barrier' on an undeclared register")
    | _ => do let (nm, i) ← parseIndexed s; .ok [⟨nm, i⟩]

/-- Parse a `barrier q[i],q[j],…` (or whole-register) body. -/
def parseBarrierStmt (prog : QASMProgram) (rest : List Char) :
    Except ParseError QASMProgram := do
  let qss ← (splitOnChar ',' rest).mapM (parseBarrierOp prog)
  .ok (addInstr prog (.barrier qss.flatten))

/-- Parse a single statement (already split off at `;`), threading the program. -/
def parseStmt (prog : QASMProgram) (seg : List Char) : Except ParseError QASMProgram :=
  let s := trimL seg
  if s.isEmpty then .ok prog
  else
    let head := takeIdent s
    match head with
    | []      => .error (.unknownStatement (String.ofList s))
    | hc :: _ =>
      if ! hc.isAlpha then .error (.unknownStatement (String.ofList s))
      else
        let headS := String.ofList head
        let rest  := trimL (dropIdent s)
        if      headS == "OPENQASM" then .ok prog                 -- header: ignore
        else if headS == "include"  then .ok prog                 -- include: accept + ignore
        else if headS == "qreg" then do
          let (nm, n) ← parseIndexed rest
          .ok { prog with qregs := prog.qregs ++ [⟨nm, n⟩] }
        else if headS == "creg" then do
          let (nm, n) ← parseIndexed rest
          .ok { prog with cregs := prog.cregs ++ [⟨nm, n⟩] }
        else if headS == "measure" then parseMeasureStmt prog rest
        else if headS == "barrier" then parseBarrierStmt prog rest
        else if headS == "h"  then parse1Q Instr.h prog rest
        else if headS == "s"  then parse1Q Instr.s prog rest
        else if headS == "sdg" then parse1QExpand (fun q => [.s q, .s q, .s q]) prog rest
        else if headS == "x"  then parse1Q Instr.x prog rest
        else if headS == "z"  then parse1Q Instr.z prog rest
        else if headS == "t"  then parse1Q Instr.t prog rest
        else if headS == "tdg" then
          parse1QExpand (fun q => [.t q, .t q, .t q, .t q, .t q, .t q, .t q]) prog rest
        else if headS == "cx" then parse2Q Instr.cx prog rest
        else if headS == "cz" then parse2Q Instr.cz prog rest
        else .ok (addInstr prog (.unsupported headS))             -- out-of-contract gate: never dropped

/-- Fold the statement parser over all `;`-separated segments.  Tail-recursive for
    benchmark-sized normalized QASM files with many statements. -/
def parseStmts (prog : QASMProgram) (segs : List (List Char)) : Except ParseError QASMProgram :=
  segs.foldlM parseStmt prog

/-! ## §4. Public entry points. -/

/-- **The OpenQASM-2 text parser.**  Strips line comments, splits on `;`, and parses each
    statement to the checked `QASMProgram` AST.  Returns a `QASMProgram` ONLY — it performs
    no logical allocation (that is `compileQASMToMixIR?`'s job). -/
def parseOpenQASM2? (src : String) : Except ParseError QASMProgram :=
  match parseStmts ⟨[], [], []⟩ (splitOnChar ';' (stripComments false src.toList)) with
  | .ok prog => .ok { prog with instrs := prog.instrs.reverse }
  | .error e => .error e

/-- A front-end error that distinguishes the PARSE phase from the ALLOCATION/LOWERING phase. -/
inductive FrontendError where
  | parse   (e : ParseError)
  | compile (e : QASMError)
  deriving Repr

/-- **Parse + allocate + compile** an OpenQASM-2 source string end to end.  Parse failures
    surface as `.parse`, allocation/lowering failures as `.compile`, so the caller can tell
    which phase rejected the program. -/
def compileOpenQASM2ToMixIR? (ws : List Compiler.CodeSwitch.CapabilityWitness) (src : String)
    (req : AllocationRequest) : Except FrontendError (QASMArtifact ws) :=
  match parseOpenQASM2? src with
  | .error e => .error (.parse e)
  | .ok prog =>
      match compileQASMToMixIR? ws prog req with
      | .ok a    => .ok a
      | .error e => .error (.compile e)

/-! ## §5. Tests — PARSING (structure), `by decide`.

    `Except` has no `DecidableEq`, so we unwrap and compare the inner program with
    `parsedTo` (`QASMProgram` gets a derived `DecidableEq` for this). -/

deriving instance DecidableEq for QASMProgram

/-- `src` parses successfully to exactly `prog`. -/
def parsedTo (src : String) (prog : QASMProgram) : Bool :=
  match parseOpenQASM2? src with
  | .ok p    => decide (p = prog)
  | .error _ => false

-- minimal: a single gate, no declarations (the parser does not require them):
example : parsedTo "h q[0];"
    { qregs := [], cregs := [], instrs := [.h ⟨"q", 0⟩] } = true := by decide

-- all supported single-/two-qubit gates parse in order:
example : parsedTo "s q[0]; z q[1]; t q[0]; cz q[0],q[1];"
    { qregs := [], cregs := [],
      instrs := [.s ⟨"q", 0⟩, .z ⟨"q", 1⟩, .t ⟨"q", 0⟩, .cz ⟨"q", 0⟩ ⟨"q", 1⟩] } = true := by decide

-- exact Qiskit aliases are expanded before allocation:
example : parsedTo "sdg q[0];"
    { qregs := [], cregs := [],
      instrs := [.s ⟨"q", 0⟩, .s ⟨"q", 0⟩, .s ⟨"q", 0⟩] } = true := by decide
example : parsedTo "tdg q[0];"
    { qregs := [], cregs := [],
      instrs := [.t ⟨"q", 0⟩, .t ⟨"q", 0⟩, .t ⟨"q", 0⟩, .t ⟨"q", 0⟩,
                 .t ⟨"q", 0⟩, .t ⟨"q", 0⟩, .t ⟨"q", 0⟩] } = true := by decide

-- a full Bell-style program: header, include, comment, qreg/creg, h/cx/measure, newlines:
def bellSrc : String :=
  "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[2];\ncreg c[2];\nh q[0]; // hadamard\ncx q[0],q[1];\nmeasure q[0] -> c[0];\nmeasure q[1] -> c[1];\n"
example : parsedTo bellSrc
    { qregs := [⟨"q", 2⟩], cregs := [⟨"c", 2⟩],
      instrs := [.h ⟨"q", 0⟩, .cx ⟨"q", 0⟩ ⟨"q", 1⟩,
                 .measure ⟨"q", 0⟩ ⟨"c", 0⟩, .measure ⟨"q", 1⟩ ⟨"c", 1⟩] } = true := by decide

-- whitespace / extra spaces / no trailing newline all parse the same:
example : parsedTo "   h   q[0]  ;x q[1] ;"
    { qregs := [], cregs := [], instrs := [.h ⟨"q", 0⟩, .x ⟨"q", 1⟩] } = true := by decide

-- comments are ignored, and a `;` INSIDE a comment does not split a statement:
example : parsedTo "x q[0]; // a ; b ; c\nz q[0];"
    { qregs := [], cregs := [], instrs := [.x ⟨"q", 0⟩, .z ⟨"q", 0⟩] } = true := by decide

-- `include "qelib1.inc";` alone is accepted and contributes nothing:
example : parsedTo "include \"qelib1.inc\";"
    { qregs := [], cregs := [], instrs := [] } = true := by decide

-- `barrier` with a list and with a whole register (expanded against the prior `qreg`):
example : parsedTo "barrier q[0],q[1];"
    { qregs := [], cregs := [], instrs := [.barrier [⟨"q", 0⟩, ⟨"q", 1⟩]] } = true := by decide
example : parsedTo "qreg q[2]; barrier q;"
    { qregs := [⟨"q", 2⟩], cregs := [], instrs := [.barrier [⟨"q", 0⟩, ⟨"q", 1⟩]] } = true := by decide

/-! ## §6. Tests — UNSUPPORTED gates parse to `.unsupported` (never dropped). -/

example : parsedTo "rx(0.3) q[0];"
    { qregs := [], cregs := [], instrs := [.unsupported "rx"] } = true := by decide
example : parsedTo "u3(0,0,0) q[0];"
    { qregs := [], cregs := [], instrs := [.unsupported "u3"] } = true := by decide
example : parsedTo "reset q[0];"
    { qregs := [], cregs := [], instrs := [.unsupported "reset"] } = true := by decide
example : parsedTo "if (c==1) x q[0];"
    { qregs := [], cregs := [], instrs := [.unsupported "if"] } = true := by decide
example : parsedTo "ccx q[0],q[1],q[2];"
    { qregs := [], cregs := [], instrs := [.unsupported "ccx"] } = true := by decide

/-! ## §7. Tests — PARSE ERRORS (malformed syntax / bad integers). -/

-- missing ']':
example : (match parseOpenQASM2? "qreg q[;" with | .error _ => true | .ok _ => false) = true := by decide
-- missing brackets entirely:
example : (match parseOpenQASM2? "qreg q 2;" with | .error _ => true | .ok _ => false) = true := by decide
-- a non-numeric index is a `badInt`:
example : (match parseOpenQASM2? "h q[a];" with | .error (.badInt _) => true | _ => false) = true := by decide
-- an empty index is a `badInt`:
example : (match parseOpenQASM2? "qreg q[];" with | .error (.badInt _) => true | _ => false) = true := by decide
-- a statement that is not gate-shaped is `unknownStatement`:
example : (match parseOpenQASM2? "[0] q;" with | .error (.unknownStatement _) => true | _ => false) = true := by decide
-- a malformed measure (no arrow):
example : (match parseOpenQASM2? "measure q[0] c[0];" with | .error (.malformed _) => true | _ => false) = true := by decide

/-! ## §8. Tests — END TO END (parse + allocate + compile). -/

-- bare/register fixture (reqHM): `H; measure` teleports through the |0⟩ ancilla `a0`:
example : ok? (compileOpenQASM2ToMixIR? []
    "qreg q[1]; creg c[1]; h q[0]; measure q[0] -> c[0];" reqHM) = true := by decide

-- a fresh measurement CVar is assigned after allocation (N = 2 ops ⇒ CVar = 3·2 + 0 = 6):
example :
    (match compileOpenQASM2ToMixIR? []
        "qreg q[1]; creg c[1]; x q[0]; measure q[0] -> c[0];" reqSurface2 with
     | .ok a    => a.alloc.measMap
     | .error _ => []) = [(⟨"c", 0⟩, 6)] := by decide

-- surface code d=2: logical Pauli + readout compiles with no gadget ancillas:
example : ok? (compileOpenQASM2ToMixIR? []
    "qreg q[1]; creg c[1]; x q[0]; measure q[0] -> c[0];" reqSurface2) = true := by decide

-- toric code d=2: two logicals, Paulis + readout:
example : ok? (compileOpenQASM2ToMixIR? []
    "qreg q[2]; creg c[2]; x q[0]; z q[1]; measure q[0] -> c[0]; measure q[1] -> c[1];"
    reqToric2) = true := by decide

-- `T` on the bare register produces a magic obligation:
example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[1]; t q[0];" reqT) = true := by decide

/-! ## §9. Tests — END TO END negatives (phase-distinguished rejection). -/

-- an unsupported gate is REJECTED at the COMPILE phase (parse succeeds, allocator rejects):
example :
    (match compileOpenQASM2ToMixIR? [] "qreg q[1]; rx(0.3) q[0];" reqHM with
     | .error (.compile (.unsupportedGate _)) => true
     | _ => false) = true := by decide
-- … even when not first in the stream:
example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[1]; x q[0]; reset q[0];" reqHM) = false := by decide

-- malformed syntax is rejected at the PARSE phase:
example :
    (match compileOpenQASM2ToMixIR? [] "qreg q[;" reqHM with
     | .error (.parse _) => true
     | _ => false) = true := by decide

-- duplicate qreg / creg still fail (through allocation, not the parser):
example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[1]; qreg q[1]; x q[0];" reqHM) = false := by decide
example : ok? (compileOpenQASM2ToMixIR? []
    "qreg q[1]; creg c[1]; creg c[1]; measure q[0] -> c[0];" reqHM) = false := by decide

-- an out-of-range qubit reference is rejected (the allocator validates references):
example : ok? (compileOpenQASM2ToMixIR? [] "qreg q[1]; h q[5];" reqHM) = false := by decide

end Compiler.QASM
