/-
  QStab.Parse — a TOTAL text parser for the QStab physical stabilizer-measurement IR
  (level L_QStab), realising the BNF in `QStab/Syntax.lean`:

      QVar      ::= c0 | c1 | …                      -- classical variable (bound in order)
      PauliStr  ::= ('I'|'X'|'Y'|'Z')+               -- dense physical Pauli, e.g. ZZI
      Sched     ::= '[' 'r' '=' Nat ',' 's' '=' Nat ']'
      Stmt      ::= QVar '=' 'Prop' Sched? PauliStr  -- physical measurement
                  | QVar '=' 'Parity' QVar+           -- classical XOR
      Prog      ::= Stmt*                             -- statements on newlines / ';'

  Text → `QStab.Prog` (the checked AST in `Syntax.lean`).  Reuses the shared char-list
  lexers (`Parsing.Basic`), so the parse tests are `by decide`.
-/
import QStab.Syntax
import Parsing.Basic

namespace QStab.Parse
open Parsing
open Physical

set_option maxRecDepth 10000

/-- Parse a schedule body `r = .. , s = ..` (the content between `[` `]`). -/
def parseSched (content : List Char) : Except ParseError QStab.Sched :=
  match splitOnChar ',' content with
  | [a, b] =>
      let val (seg : List Char) : Option Nat :=
        match splitOnChar '=' seg with
        | [_, v] => natOfDigits? (trimL v)
        | _      => none
      match val a, val b with
      | some r, some s => .ok ⟨r, s⟩
      | _, _ => .error (.malformed "bad schedule '[r=.., s=..]'")
  | _ => .error (.malformed "schedule must be '[r=.., s=..]'")

/-- Parse a dense Pauli token like `ZZI` (any non-`X/Y/Z` letter is `I`). -/
def parsePauliStr (cs : List Char) : Except ParseError QStab.PauliString :=
  match trimL cs with
  | [] => .error (.malformed "expected a Pauli string")
  | t  => .ok (t.map Pauli.ofChar)

/-- Parse the RHS of a `Prop` statement: an optional schedule then a Pauli token. -/
def parsePropRHS (rest : List Char) : Except ParseError QStab.Stmt :=
  match trimL rest with
  | '[' :: rest2 =>
      match spanUntil ']' rest2 with
      | some (content, after) => do
          let sched ← parseSched content
          let P ← parsePauliStr after
          .ok (.prop (some sched) P)
      | none => .error (.malformed "missing ']' in schedule")
  | s => do
      let P ← parsePauliStr s
      .ok (.prop none P)

/-- Parse the RHS of a `Parity` statement: a (comma/space-separated) list of variable
    NAMES, each resolved to its binding POSITION via the running name table `names`
    (variables bind in program order, so a `parity` also consumes a position — `c3` may be
    position 4 if parities precede it). -/
def parseParityRHS (names : List String) (rest : List Char) : Except ParseError QStab.Stmt :=
  let toks := ((splitOnChar ',' rest).flatMap (splitOnChar ' ')).filter (fun t => ! (trimL t).isEmpty)
  let resolve (t : List Char) : Option Nat := nameIndex? names (String.ofList (trimL t))
  match toks.mapM resolve with
  | some xs => .ok (.parity xs)
  | none    => .error (.malformed "Parity references an unbound variable")

/-- Parse one statement (already split off at a newline/`;`), threading the running
    name→position table and the reversed statement accumulator. -/
def parseStmt (st : List String × List QStab.Stmt) (seg : List Char) :
    Except ParseError (List String × List QStab.Stmt) :=
  let (names, acc) := st
  let s := trimL seg
  if s.isEmpty then .ok st
  else
    match spanUntil '=' s with          -- split at the FIRST '=' (schedule '='s stay in the RHS)
    | some (lhs, rhs) =>
        let nm   := String.ofList (trimL lhs)
        let rhsT := trimL rhs
        let head := String.ofList (takeIdent rhsT)
        let rest := trimL (dropIdent rhsT)
        if      head == "Prop"   then do let stm ← parsePropRHS rest;         .ok (names ++ [nm], stm :: acc)
        else if head == "Parity" then do let stm ← parseParityRHS names rest; .ok (names ++ [nm], stm :: acc)
        else .error (.unknownStatement (String.ofList s))
    | none => .error (.unknownStatement (String.ofList s))

/-- **Parse QStab text to a `QStab.Prog`.** -/
def parseQStab (src : String) : Except ParseError QStab.Prog :=
  match (stmtSegments src).foldlM parseStmt ([], []) with
  | .ok (_, rev) => .ok rev.reverse
  | .error e     => .error e

/-! ## Tests — `by decide`. -/

/-- `src` parses to exactly `prog`. -/
def parsesTo (src : String) (prog : QStab.Prog) : Bool :=
  match parseQStab src with
  | .ok p    => decide (p = prog)
  | .error _ => false

-- the README distance-3 readout program parses to exactly `QStab.progReadout`:
def readoutSrc : String :=
  "c0 = Prop[r=0,s=0] ZZI\nc1 = Prop[r=0,s=1] IZZ\nc2 = Prop[r=1,s=0] ZZI\nd0 = Parity c0 c2\nc3 = Prop[r=1,s=1] IZZ\nd1 = Parity c1 c3\nc4 = Prop ZZZ\no0 = Parity c4"
example : parsesTo readoutSrc QStab.progReadout = true := by decide

-- and the parsed program is well-formed:
example : (match parseQStab readoutSrc with | .ok p => p.wf | .error _ => false) = true := by decide

-- comma-separated parity sources and unscheduled props also parse:
example : parsesTo "c0 = Prop XIX\nd0 = Parity c0, c0"
    [.prop none (ofString "XIX"), .parity [0, 0]] = true := by decide

-- an unrecognized head is a structured error:
example : (match parseQStab "c0 = Frobnicate ZZ" with | .error (.unknownStatement _) => true | _ => false) = true := by decide

end QStab.Parse
