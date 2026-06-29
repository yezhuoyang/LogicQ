/-
  Compiler.Mixed.Parse — TOTAL text parsers for the two keyword-led languages of the
  middle of the stack, realising the constructors of `Compiler/Mixed/Syntax.lean` as
  surface keywords:

  ── LOGICAL source language (`LogicalOp`) ──────────────────────────────────────────────
    EVERY logical instruction is prefixed with the `Logical` keyword (a program of bare
    gates is rejected):

      LStmt ::= 'Logical' ( 'H'|'S'|'T'|'X'|'Z' ) q[i]              -- one-logical-qubit gate
              | 'Logical' ( 'CNOT'|'CZ' ) q[i] q[j]                  -- two-logical-qubit gate
              | 'Logical' 'measure' MTarget '->' c<n>               -- logical Pauli-product measurement

  ── MIXED IR (`MixedInstr`) ────────────────────────────────────────────────────────────
    EVERY mixed instruction LEADS with its KIND keyword (the discriminating constructor):

      MStmt ::= 'transversal' <block> ( 'H' | 'S' )                  -- MixedInstr.transversal b g
              | 'transversalCNOT' q[i] q[j] <incidence-matrix>       -- MixedInstr.transversalCNOT
              | 'pauli' ( 'X'|'Y'|'Z' ) q[i]                         -- MixedInstr.pauli q p
              | 'magic' 'T' q[i]                                     -- MixedInstr.magic (T obligation)
              | 'ppm' <PPM statement>                                -- MixedInstr.ppm s

    (`automorphism`, `switch`, and `transversalCNOTBatch` carry a full BoolMat / Block /
    SwitchCert payload and stay machine-form for now — the next increment.)

  Block names (`q`, `a`, …) intern to `Logical.BlockId`s in first-occurrence order; block
  ids in `transversal` are bare naturals.  Text → `List LogicalOp` / `List MixedInstr`,
  reusing the shared lexers (`Parsing.Basic`) and the PPM target parser; the Logical tests
  are `by decide`, the Mixed tests pattern-match the parsed constructor.
-/
import Compiler.Mixed.Syntax
import PPM.Parse

namespace Compiler.Mixed.Parse
open Compiler TypeChecker PPM ChainQ.GF2 Logical Parsing

set_option maxRecDepth 10000

/-! ## §1. Shared operand parsing. -/

/-- Parse one qubit token `q[i]`, interning its block name. -/
def qubit1 (names : List String) (cs : List Char) : Except ParseError (List String × LQubit) := do
  let (nm, idx) ← parseIndexed cs
  let (names', bid) := internName names nm
  .ok (names', ⟨bid, idx⟩)

/-- Parse two space-separated qubit tokens `q[i] q[j]`. -/
def qubit2 (names : List String) (cs : List Char) : Except ParseError (List String × LQubit × LQubit) :=
  match (splitOnChar ' ' cs).filter (fun t => ! (trimL t).isEmpty) with
  | [a, b] => do
      let (n1, q1) ← qubit1 names a
      let (n2, q2) ← qubit1 n1 b
      .ok (n2, q1, q2)
  | _ => .error (.malformed "expected two qubits 'q[i] q[j]'")

/-! ## §2. The LOGICAL source language — every instruction carries the `Logical` keyword. -/

/-- Parse one `Logical …` statement, threading the block-name table. -/
def parseLogicalStmt (st : List String × List LogicalOp) (seg : List Char) :
    Except ParseError (List String × List LogicalOp) :=
  let (names, acc) := st
  let s := trimL seg
  if s.isEmpty then .ok st
  else if String.ofList (takeIdent s) != "Logical" then
    .error (.unknownStatement
      ("every logical instruction must start with the `Logical` keyword: " ++ String.ofList s))
  else
    let afterKw := trimL (dropIdent s)
    let op   := String.ofList (takeIdent afterKw)
    let args := trimL (dropIdent afterKw)
    let one (mk : LQubit → LogicalOp) : Except ParseError (List String × List LogicalOp) := do
      let (names', q) ← qubit1 names args; .ok (names', mk q :: acc)
    let two (mk : LQubit → LQubit → LogicalOp) : Except ParseError (List String × List LogicalOp) := do
      let (names', q1, q2) ← qubit2 names args; .ok (names', mk q1 q2 :: acc)
    if      op == "H" then one .hGate
    else if op == "S" then one .sGate
    else if op == "T" then one .tGate
    else if op == "X" then one .xGate
    else if op == "Z" then one .zGate
    else if op == "CNOT" then two .cnotGate
    else if op == "CZ"   then two .czGate
    else if op == "measure" then
      match spanArrow args with
      | some (lhs, rhs) => do
          let (names', tgt) ← PPM.Parse.parseMTarget names lhs
          match parseTaggedNat? 'c' rhs with
          | some r => .ok (names', .measure r tgt :: acc)
          | none => .error (.malformed "expected a result var 'c<n>' after '->'")
      | none => .error (.malformed "expected 'Logical measure <target> -> c<n>'")
    else .error (.unknownStatement ("unknown Logical op: " ++ op))

/-- **Parse a `Logical` program to `List LogicalOp`.** -/
def parseLogical (src : String) : Except ParseError (List LogicalOp) :=
  match (stmtSegments src).foldlM parseLogicalStmt ([], []) with
  | .ok (_, rev) => .ok rev.reverse
  | .error e     => .error e

/-! ## §3. The MIXED IR — every instruction leads with its KIND keyword. -/

/-- A gate name's 2×2 symplectic matrix (`H`/`S`). -/
def gateMat? (nm : String) : Option BoolMat :=
  if nm == "H" then some hGate2x2 else if nm == "S" then some sGate2x2 else none

/-- A single 0/1 cell. -/
def boolCell? (cs : List Char) : Option Bool :=
  match trimL cs with | '1' :: _ => some true | '0' :: _ => some false | _ => none

/-- A comma-separated 0/1 row. -/
def boolRow? (cs : List Char) : Option (List Bool) :=
  ((splitOnChar ',' cs).filter (fun t => ! (trimL t).isEmpty)).mapM boolCell?

/-- Extract successive bracketed rows `[ … ]` (fuelled by the remaining length). -/
def rowsAux : Nat → List Char → Option (List (List Bool))
  | 0,        _  => some []
  | fuel + 1, cs =>
    match spanUntil '[' cs with
    | none => some []
    | some (_, afterOpen) =>
      match spanUntil ']' afterOpen with
      | none => none
      | some (row, afterClose) =>
        match boolRow? row, rowsAux fuel afterClose with
        | some r, some rs => some (r :: rs)
        | _, _ => none

/-- Parse a 0/1 matrix literal `[[1,0],[0,1]]` to a `BoolMat` (spaces ignored). -/
def parseBoolMat? (cs0 : List Char) : Option BoolMat :=
  match (trimL cs0).filter (fun c => c != ' ') with
  | '[' :: rest =>
      match rest.reverse with
      | ']' :: midRev => rowsAux (midRev.length + 1) midRev.reverse
      | _ => none
  | _ => none

/-- Parse one mixed-IR statement (KIND keyword first), threading the block-name table. -/
def parseMixedStmt (st : List String × List MixedInstr) (seg : List Char) :
    Except ParseError (List String × List MixedInstr) :=
  let (names, acc) := st
  let s := trimL seg
  if s.isEmpty then .ok st
  else
    let kind := String.ofList (takeIdent s)
    let args := trimL (dropIdent s)
    if kind == "transversal" then
      match (splitOnChar ' ' args).filter (fun t => ! (trimL t).isEmpty) with
      | [bcs, gcs] =>
          match natOfDigits? (trimL bcs), gateMat? (String.ofList (trimL gcs)) with
          | some b, some g => .ok (names, .transversal b g :: acc)
          | _, _ => .error (.malformed "expected 'transversal <block> <H|S>'")
      | _ => .error (.malformed "expected 'transversal <block> <gate>'")
    else if kind == "pauli" then
      match (splitOnChar ' ' args).filter (fun t => ! (trimL t).isEmpty) with
      | [pcs, qcs] =>
          match PPM.Parse.pletter? pcs with
          | some p => do let (names', q) ← qubit1 names qcs; .ok (names', .pauli q p :: acc)
          | none => .error (.malformed "expected a Pauli letter in 'pauli <P> q[i]'")
      | _ => .error (.malformed "expected 'pauli <P> q[i]'")
    else if kind == "magic" then
      match (splitOnChar ' ' args).filter (fun t => ! (trimL t).isEmpty) with
      | [gcs, qcs] =>
          if String.ofList (trimL gcs) == "T" then do
            let (names', q) ← qubit1 names qcs
            .ok (names', .magic { kind := .tGate, target := q } :: acc)
          else .error (.malformed "only 'magic T q[i]' is supported")
      | _ => .error (.malformed "expected 'magic T q[i]'")
    else if kind == "transversalCNOT" then
      match (splitOnChar ' ' args).filter (fun t => ! (trimL t).isEmpty) with
      | [q1cs, q2cs, mcs] => do
          let (n1, c) ← qubit1 names q1cs
          let (n2, t) ← qubit1 n1 q2cs
          match parseBoolMat? mcs with
          | some inc => .ok (n2, .transversalCNOT { control := c, target := t, incidence := inc } :: acc)
          | none => .error (.malformed "bad incidence matrix in 'transversalCNOT q[i] q[j] [[..]]'")
      | _ => .error (.malformed "expected 'transversalCNOT q[i] q[j] [[..]]'")
    else if kind == "ppm" then
      match PPM.Parse.parsePPM (String.ofList args) with
      | .ok [stm] => .ok (names, .ppm stm :: acc)
      | .ok _     => .error (.malformed "'ppm' expects a single PPM statement")
      | .error e  => .error e
    else .error (.unknownStatement
      ("unknown mixed-IR kind keyword: " ++ kind ++
       " (expected transversal/transversalCNOT/pauli/magic/ppm)"))

/-- **Parse a mixed-IR program to `List MixedInstr`.** -/
def parseMixed (src : String) : Except ParseError (List MixedInstr) :=
  match (stmtSegments src).foldlM parseMixedStmt ([], []) with
  | .ok (_, rev) => .ok rev.reverse
  | .error e     => .error e

/-! ## §4. Tests — LOGICAL (`by decide`; `LogicalOp` has `DecidableEq`). -/

/-- `src` parses to exactly `ops`. -/
def logicalParsesTo (src : String) (ops : List LogicalOp) : Bool :=
  match parseLogical src with | .ok p => decide (p = ops) | .error _ => false

-- the user's example: a two-qubit logical CNOT carries the `Logical` keyword:
example : logicalParsesTo "Logical CNOT q[0] q[1]" [.cnotGate ⟨0, 0⟩ ⟨0, 1⟩] = true := by decide

-- a fuller logical program (gates + a logical measurement), each `Logical`-prefixed:
example : logicalParsesTo "Logical H q[0]\nLogical T q[0]\nLogical measure q[0]↦Z -> c0"
    [.hGate ⟨0, 0⟩, .tGate ⟨0, 0⟩, .measure 0 [(⟨0, 0⟩, .Z)]] = true := by decide

-- a CNOT across two code blocks (q ↦ 0, r ↦ 1):
example : logicalParsesTo "Logical CNOT q[0] r[0]" [.cnotGate ⟨0, 0⟩ ⟨1, 0⟩] = true := by decide

-- the `Logical` keyword is REQUIRED — a bare gate is rejected:
example : (match parseLogical "H q[0]" with | .error (.unknownStatement _) => true | _ => false) = true := by decide

/-! ## §5. Tests — MIXED IR (pattern-match the parsed KIND keyword). -/

-- `transversal 0 H` is a block-0 direct transversal (g = hGate2x2):
example : (match parseMixed "transversal 0 H" with
            | .ok [.transversal 0 [[false, true], [true, false]]] => true | _ => false) = true := by decide

-- `pauli X q[0]` is a logical Pauli applied to the carrier:
example : (match parseMixed "pauli X q[0]" with
            | .ok [.pauli ⟨0, 0⟩ .X] => true | _ => false) = true := by decide

-- `magic T q[0]` is a deferred T obligation:
example : (match parseMixed "magic T q[0]" with
            | .ok [.magic ⟨.tGate, ⟨0, 0⟩, _⟩] => true | _ => false) = true := by decide

-- `ppm …` wraps a native PPM statement:
example : (match parseMixed "ppm c0 := M q[0]↦Z" with
            | .ok [.ppm (.meas 0 [(⟨0, 0⟩, .Z)])] => true | _ => false) = true := by decide

-- `transversalCNOT q[0] q[1] [[1]]` carries its incidence matrix:
example : (match parseMixed "transversalCNOT q[0] q[1] [[1]]" with
            | .ok [.transversalCNOT ⟨⟨0, 0⟩, ⟨0, 1⟩, [[true]]⟩] => true | _ => false) = true := by decide

-- a missing kind keyword is rejected (mixed instructions must lead with their kind):
example : (match parseMixed "H q[0]" with | .error (.unknownStatement _) => true | _ => false) = true := by decide

end Compiler.Mixed.Parse
