/-
  Compiler.Surface.Parse — a small, TOTAL textual front-end for the LogicQ **surface
  language** (`.lqr`), layered on the verified OpenQASM → MixIR backend.

  This realises the "human-readable program text → IR" goal: a real parser that reads the
  surface syntax and compiles it end to end through the already-verified
  `Compiler.QASM.compileQASMToMixIR?` pipeline (no new, unverified lowering).

  BNF (v0 core — the subset that parses AND compiles today):

      Program  ::= Stmt*                              -- statements separated by newline or ';'
      Stmt     ::= 'code' Id 'as' 'Bare'              -- declare bare data blocks
                 | ('H' | 'S' | 'T' | 'X' | 'Z') Qubit
                 | 'CNOT' Qubit ',' Qubit
                 | 'CZ'   Qubit ',' Qubit
                 | 'measure' Qubit '->' Cbit
      Qubit    ::= Id '[' Nat ']'                     -- e.g. q[0]
      Cbit     ::= Id '[' Nat ']'                     -- e.g. c[0]
      -- '// …' line comments are stripped before parsing.

  It parses `.lqr` text to the checked `Compiler.QASM.QASMProgram` AST and compiles it on
  bare `[[1,1,1]]` blocks (one logical = one physical) through `compileQASMToMixIR?`.

  HONEST SCOPE (v0).  Only the `Bare` code family is wired into THIS front-end; a
  `code … as Surface(3)` (etc.) is a clear parse error here.  Richer code families are
  declarable today via the ChainQ `code … as LiftedProduct { … }` / `indexed_css { … }`
  macros (`ChainQ/SurfaceSyntax.lean`); wiring them into this front-end (so a `.lqr`
  program can name a surface/toric/LP code) is the next increment.

  DECIDABILITY.  Parsing is over `List Char` (reusing the QASM helpers), so every
  parse/compile test below is `by decide`-checkable.
-/
import Compiler.QASM.Parse

namespace Compiler.Surface
open Compiler.QASM

set_option maxRecDepth 10000

/-! ## §1. Statement parsing (reuses the QASM char-list helpers). -/

/-- Parse a `code <id> as Bare` declaration.  v0 wires ONLY the `Bare` family. -/
def parseCodeDecl (rest : List Char) : Except ParseError Unit :=
  let afterName := trimL (dropIdent (trimL rest))
  match String.ofList (takeIdent afterName) with
  | "as" =>
      match String.ofList (takeIdent (trimL (dropIdent afterName))) with
      | "Bare" => .ok ()
      | fam    => .error (.malformed
          s!"surface front-end v0 wires only `code <id> as Bare` (got `{fam}`); richer code families use the ChainQ `code … as …` macros")
  | _ => .error (.malformed "expected `code <id> as Bare`")

/-- Parse one surface statement (already split off at a newline / `;`), prepending the
    resulting QASM `Instr`(s) to the reversed accumulator. -/
def parseLqrStmt (acc : List Instr) (seg : List Char) : Except ParseError (List Instr) :=
  let s := trimL seg
  if s.isEmpty then .ok acc
  else
    let head := String.ofList (takeIdent s)
    let rest := trimL (dropIdent s)
    let one (mk : VQubit → Instr) : Except ParseError (List Instr) := do
      let (nm, i) ← parseIndexed rest
      .ok (mk ⟨nm, i⟩ :: acc)
    let two (mk : VQubit → VQubit → Instr) : Except ParseError (List Instr) :=
      match splitOnChar ',' rest with
      | [a, b] => do
          let (n1, i1) ← parseIndexed a
          let (n2, i2) ← parseIndexed b
          .ok (mk ⟨n1, i1⟩ ⟨n2, i2⟩ :: acc)
      | _ => .error (.malformed "expected two comma-separated qubits")
    if      head == "code"    then do let _ ← parseCodeDecl rest; .ok acc
    else if head == "H"       then one Instr.h
    else if head == "S"       then one Instr.s
    else if head == "T"       then one Instr.t
    else if head == "X"       then one Instr.x
    else if head == "Z"       then one Instr.z
    else if head == "CNOT"    then two Instr.cx
    else if head == "CZ"      then two Instr.cz
    else if head == "measure" then
      match spanArrow rest with
      | some (lhs, rhs) => do
          let (qn, qi) ← parseIndexed lhs
          let (cn, ci) ← parseIndexed rhs
          .ok (Instr.measure ⟨qn, qi⟩ ⟨cn, ci⟩ :: acc)
      | none => .error (.malformed "expected `measure q[i] -> c[j]`")
    else .error (.unknownStatement (String.ofList s))

/-- Split surface source into statement segments on newlines and `;`, comments stripped. -/
def lqrSegments (src : String) : List (List Char) :=
  ((splitOnChar '\n' (stripComments false src.toList)).flatMap (splitOnChar ';')).filter
    (fun s => ! (trimL s).isEmpty)

/-- **Parse `.lqr` text to a `QASMProgram` instruction list** (source order). -/
def parseLqr (src : String) : Except ParseError (List Instr) :=
  match (lqrSegments src).foldlM parseLqrStmt [] with
  | .ok rev  => .ok rev.reverse
  | .error e => .error e

/-! ## §2. Register inference + the bare allocation request. -/

/-- Infer the `qreg`s used by the program (one entry per register name, sized to its max
    index + 1). -/
def collectQRegs (instrs : List Instr) : List QReg :=
  let refs := instrs.flatMap Instr.qubitRefs
  let names := refs.foldl (fun a q => if a.contains q.reg then a else a ++ [q.reg]) ([] : List String)
  names.map (fun nm => { name := nm, size := refs.foldl (fun m q => if q.reg == nm then Nat.max m (q.idx + 1) else m) 0 })

/-- Infer the `creg`s used by the program (from measurement targets). -/
def collectCRegs (instrs : List Instr) : List CReg :=
  let refs := instrs.flatMap Instr.cbitRefs
  let names := refs.foldl (fun a c => if a.contains c.reg then a else a ++ [c.reg]) ([] : List String)
  names.map (fun nm => { name := nm, size := refs.foldl (fun m c => if c.reg == nm then Nat.max m (c.idx + 1) else m) 0 })

/-- A bare allocation request: `n` separate `[[1,1,1]]` data blocks (one logical = one
    physical), transversal CNOT enabled — the same shape the bare QASMBench suite uses. -/
def bareReq (n : Nat) : AllocationRequest :=
  { decls        := (List.range n).map (fun i => { ChainQ.indexedBareDecl with name := "q" ++ toString i })
    dataLogicals := (List.range n).map (fun i => { code := "q" ++ toString i, logical := "data" })
    ancillas     := []
    cnotMode     := .strictTransversal
    cnotIncidence := some [[true]] }

/-- The `QASMProgram` a surface program denotes (inferred regs + the parsed instructions). -/
def lqrProgram (instrs : List Instr) : QASMProgram :=
  { qregs := collectQRegs instrs, cregs := collectCRegs instrs, instrs := instrs }

/-! ## §3. End-to-end: `.lqr` text → MixIR (parse + allocate + compile). -/

/-- **Parse + allocate + compile** a `.lqr` source string to MixIR, on bare blocks.  Parse
    failures surface as `.parse`, allocation/lowering failures as `.compile`. -/
def compileSurfaceToMixIR? (ws : List Compiler.CodeSwitch.CapabilityWitness) (src : String) :
    Except FrontendError (QASMArtifact ws) :=
  match parseLqr src with
  | .error e => .error (.parse e)
  | .ok instrs =>
      let prog := lqrProgram instrs
      let n := prog.qregs.foldl (fun a r => a + r.size) 0
      match compileQASMToMixIR? ws prog (bareReq n) with
      | .ok a    => .ok a
      | .error e => .error (.compile e)

/-! ## §4. Tests — PARSE (structure), `by decide`. -/

/-- `src` parses to exactly `instrs`. -/
def parsesTo (src : String) (instrs : List Instr) : Bool :=
  match parseLqr src with
  | .ok is   => decide (is = instrs)
  | .error _ => false

-- a flip + read program (note: `q[0]` / `c[0]` brackets, per the BNF):
example : parsesTo "X q[0]\nmeasure q[0] -> c[0]"
    [.x ⟨"q", 0⟩, .measure ⟨"q", 0⟩ ⟨"c", 0⟩] = true := by decide

-- a Bell pair, with a `code` decl, comments, and `;`/newline separators:
example : parsesTo "code q as Bare\nH q[0]; CNOT q[0], q[1]  // entangle\nmeasure q[0] -> c[0]\nmeasure q[1] -> c[1]"
    [.h ⟨"q", 0⟩, .cx ⟨"q", 0⟩ ⟨"q", 1⟩,
     .measure ⟨"q", 0⟩ ⟨"c", 0⟩, .measure ⟨"q", 1⟩ ⟨"c", 1⟩] = true := by decide

-- all single-qubit gates + CZ parse in order:
example : parsesTo "H q[0]; S q[0]; T q[0]; X q[0]; Z q[0]; CZ q[0], q[1]"
    [.h ⟨"q",0⟩, .s ⟨"q",0⟩, .t ⟨"q",0⟩, .x ⟨"q",0⟩, .z ⟨"q",0⟩, .cz ⟨"q",0⟩ ⟨"q",1⟩] = true := by decide

-- an unknown keyword is a structured parse error (never silently dropped):
example : (match parseLqr "FOO q[0]" with | .error (.unknownStatement _) => true | _ => false) = true := by decide
-- a non-Bare code family is REJECTED in v0 (honest):
example : (match parseLqr "code q as Surface(3)" with | .error (.malformed _) => true | _ => false) = true := by decide
-- a malformed measure (no arrow) is a parse error:
example : (match parseLqr "measure q[0] c[0]" with | .error (.malformed _) => true | _ => false) = true := by decide

/-! ## §5. Tests — END TO END (`.lqr` text → MixIR), `by decide`. -/

/-- Did the surface compile succeed? -/
def compiles? (src : String) : Bool :=
  match compileSurfaceToMixIR? [] src with | .ok _ => true | .error _ => false

-- flip + read compiles end to end on a bare block:
example : compiles? "X q[0]\nmeasure q[0] -> c[0]" = true := by decide
-- a Bell pair (H + transversal CNOT + two readouts) compiles on bare blocks:
example : compiles? "code q as Bare\nH q[0]\nCNOT q[0], q[1]\nmeasure q[0] -> c[0]\nmeasure q[1] -> c[1]" = true := by decide
-- a non-Bare family fails at the PARSE phase (phase-distinguished):
example : (match compileSurfaceToMixIR? [] "code q as Surface(3)\nX q[0]" with
            | .error (.parse _) => true | _ => false) = true := by decide

end Compiler.Surface
