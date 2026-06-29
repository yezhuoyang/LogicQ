/-
  PPM.Parse — a TOTAL text parser for the QMeas measurement IR (level L_PPM), realising
  the straight-line core of the BNF in `PPM/Syntax.lean`:

      Stmt ::= r ':=' 'M' MTarget                  -- Pauli-product measurement
             | 'frame' PLetter '(' LQubit ')'      -- record a byproduct frame
             | 'discard' LQubit
             | 'skip' | 'abort'
      MTarget ::= (LQubit '↦' PLetter)*            -- comma-separated, e.g. q[0]↦Z, a[0]↦X
      LQubit  ::= Block '[' Nat ']'                -- e.g. q[0]

  Statements are newline/`;`-separated; the result is the `List PPM.Stmt` of top-level
  statements (`seqOf` folds them into one `PPM.Stmt` via `;;`).  Block names (`q`, `a`, …)
  map to `Logical.BlockId`s in first-occurrence order.  Classical variables `c<n>` are
  explicit (`c0 ↦ 0`).

  HONEST SCOPE.  This parses the straight-line measurement fragment (the README forms); the
  ADAPTIVE control (`if r = +1 then … else …`) and bounded `for` loops are recursive and
  are deferred to a later increment of this parser (they remain first-class in the AST).

  Text → `List PPM.Stmt`; reuses the shared char-list lexers (`Parsing.Basic`).
-/
import PPM.Syntax
import Parsing.Basic

namespace PPM.Parse
open Parsing
open Logical

set_option maxRecDepth 10000

/-- The Pauli letter a character denotes (`X`/`Y`/`Z`). -/
def pletterChar? (c : Char) : Option PPM.PLetter :=
  if c == 'X' then some .X else if c == 'Y' then some .Y else if c == 'Z' then some .Z else none

/-- The Pauli letter a token's first non-blank character denotes. -/
def pletter? (cs : List Char) : Option PPM.PLetter :=
  match trimL cs with
  | c :: _ => pletterChar? c
  | []     => none

/-- Parse a measurement target `(q[i] ↦ P)*` (comma-separated), threading the block-name
    table. -/
def parseMTarget (names : List String) (rest : List Char) :
    Except ParseError (List String × PPM.MTarget) :=
  let factors := (splitOnChar ',' rest).filter (fun t => ! (trimL t).isEmpty)
  factors.foldlM
    (fun (st : List String × PPM.MTarget) (f : List Char) =>
      match splitOnChar '↦' f with
      | [lhs, p] => do
          let (nm, idx) ← parseIndexed lhs
          match pletter? p with
          | some pl => let (names', bid) := internName st.1 nm
                       .ok (names', st.2 ++ [(⟨bid, idx⟩, pl)])
          | none => .error (.malformed "expected a Pauli letter X/Y/Z")
      | _ => .error (.malformed "expected 'q[i] ↦ P'"))
    (names, [])

/-- Parse a `frame PLetter '(' LQubit ')'` body, threading the block-name table. -/
def parseFrame (names : List String) (rest : List Char) :
    Except ParseError (List String × PPM.Stmt) :=
  match trimL rest with
  | pc :: rest2 =>
      match pletterChar? pc with
      | some pl =>
          match trimL rest2 with
          | '(' :: rest3 =>
              match spanUntil ')' rest3 with
              | some (content, _after) => do
                  let (nm, idx) ← parseIndexed content
                  let (names', bid) := internName names nm
                  .ok (names', .frame ⟨bid, idx⟩ pl)
              | none => .error (.malformed "missing ')' in frame")
          | _ => .error (.malformed "expected '(' in frame")
      | none => .error (.malformed "expected a Pauli letter in frame")
  | [] => .error (.malformed "empty frame")

/-- Parse one statement (split off at a newline/`;`), threading the block-name table and
    the reversed statement accumulator. -/
def parseStmt (st : List String × List PPM.Stmt) (seg : List Char) :
    Except ParseError (List String × List PPM.Stmt) :=
  let (names, acc) := st
  let s := trimL seg
  if s.isEmpty then .ok st
  else
    let headCs := takeIdent s
    let head   := String.ofList headCs
    let rest   := trimL (dropIdent s)
    match rest with
    | ':' :: '=' :: rest2 =>                          -- r := M MTarget
        let afterAssign := trimL rest2
        if String.ofList (takeIdent afterAssign) == "M" then
          match parseTaggedNat? 'c' headCs with
          | some r => do
              let (names', tgt) ← parseMTarget names (trimL (dropIdent afterAssign))
              .ok (names', .meas r tgt :: acc)
          | none => .error (.malformed "bad measurement variable")
        else .error (.malformed "expected 'M' after ':='")
    | _ =>
      if head == "frame" then do
        let (names', stm) ← parseFrame names rest
        .ok (names', stm :: acc)
      else if head == "discard" then do
        let (nm, idx) ← parseIndexed rest
        let (names', bid) := internName names nm
        .ok (names', .discard ⟨bid, idx⟩ :: acc)
      else if head == "skip"  then .ok (names, .skip  :: acc)
      else if head == "abort" then .ok (names, .abort :: acc)
      else .error (.unknownStatement (String.ofList s))

/-- **Parse PPM text to the list of top-level `PPM.Stmt`s.** -/
def parsePPM (src : String) : Except ParseError (List PPM.Stmt) :=
  match (stmtSegments src).foldlM parseStmt ([], []) with
  | .ok (_, rev) => .ok rev.reverse
  | .error e     => .error e

/-- Fold a statement list into one sequenced `PPM.Stmt` (`[]` ↦ `skip`). -/
def seqOf : List PPM.Stmt → PPM.Stmt
  | []      => .skip
  | [s]     => s
  | s :: rest => .seq s (seqOf rest)

/-! ## Tests — `by decide`. -/

/-- `src` parses to exactly `stmts`. -/
def parsesTo (src : String) (stmts : List PPM.Stmt) : Bool :=
  match parsePPM src with
  | .ok p    => decide (p = stmts)
  | .error _ => false

-- a two-body joint measurement: `q` interns to block 0, `a` to block 1:
example : parsesTo "c0 := M q[0]↦Z, a[0]↦X"
    [.meas 0 [(⟨0, 0⟩, .Z), (⟨1, 0⟩, .X)]] = true := by decide

-- a one-body measurement, a frame, and a discard:
example : parsesTo "c1 := M q[0]↦X\nframe Z(q[0])\ndiscard q[0]"
    [.meas 1 [(⟨0, 0⟩, .X)], .frame ⟨0, 0⟩ .Z, .discard ⟨0, 0⟩] = true := by decide

-- skip / abort:
example : parsesTo "skip; abort" [.skip, .abort] = true := by decide

-- the parsed (repeated-qubit) target is structurally caught by `MTarget.wf`:
example : (match parsePPM "c0 := M q[0]↦Z, q[0]↦X" with
            | .ok [.meas _ tgt] => PPM.MTarget.wf tgt
            | _ => true) = false := by decide

-- an unknown statement is a structured error:
example : (match parsePPM "frobnicate q[0]" with | .error (.unknownStatement _) => true | _ => false) = true := by decide

end PPM.Parse
