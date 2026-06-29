/-
  QClifford.Parse — a TOTAL text parser for the final QClifford target IR
  (level L_QClifford), realising the BNF in `QClifford/Syntax.lean`:

      Gate ::= 'Prep0' q | 'Prep+' q
             | 'H' q | 'S' q | 'X' q | 'Z' q
             | 'CNOT' c t | 'CZ' a b
             | 'Meas' q '->' CBit                 -- Z-basis measurement
             | CBit ':=' 'xor' CBit*               -- classical parity
             | 'If' CBit 'then' Pauli q           -- classically-conditioned Pauli
      Circuit ::= Gate*                            -- gates on newlines / ';'

  Qubits and classical bits are bare naturals; the tags `q`/`c` (e.g. `q3`, `c7`) are
  accepted and optional.  Text → `QClifford.Circuit` (the checked AST in `Syntax.lean`),
  reusing the shared char-list lexers (`Parsing.Basic`), so the parse tests are `by decide`.
-/
import QClifford.Syntax
import Parsing.Basic

namespace QClifford.Parse
open Parsing
open Physical

set_option maxRecDepth 10000

/-- The Pauli a token denotes (its first letter; non-`X/Y/Z` is `I`). -/
def pauliOf (cs : List Char) : Pauli :=
  match trimL cs with
  | c :: _ => Pauli.ofChar c
  | []     => .I

/-- Parse a one-qubit gate body `q`. -/
def oneQ (mk : PQubit → Gate) (rest : List Char) : Except ParseError Gate :=
  match parseTaggedNat? 'q' rest with
  | some q => .ok (mk q)
  | none   => .error (.malformed "expected a qubit")

/-- Parse a two-qubit gate body `a b` (or `a, b`). -/
def twoQ (mk : PQubit → PQubit → Gate) (rest : List Char) : Except ParseError Gate :=
  match ((splitOnChar ',' rest).flatMap (splitOnChar ' ')).filter (fun t => ! (trimL t).isEmpty) with
  | [a, b] =>
      match parseTaggedNat? 'q' a, parseTaggedNat? 'q' b with
      | some x, some y => .ok (mk x y)
      | _, _ => .error (.malformed "bad qubit in two-qubit gate")
  | _ => .error (.malformed "expected two qubits")

/-- Parse one gate (already split off at a newline/`;`), prepending to the reversed
    accumulator. -/
def parseGate (acc : List Gate) (seg : List Char) : Except ParseError (List Gate) :=
  let s := trimL seg
  if s.isEmpty then .ok acc
  else
    let headCs := takeIdent s
    let head   := String.ofList headCs
    let rest   := trimL (dropIdent s)
    match rest with
    | ':' :: '=' :: rest2 =>                          -- CBit := xor CBit*
        let afterAssign := trimL rest2
        if String.ofList (takeIdent afterAssign) == "xor" then
          let srcs := ((splitOnChar ',' (trimL (dropIdent afterAssign))).flatMap (splitOnChar ' ')).filter
                        (fun t => ! (trimL t).isEmpty)
          match parseTaggedNat? 'c' headCs, srcs.mapM (parseTaggedNat? 'c') with
          | some tgt, some xs => .ok (.parity tgt xs :: acc)
          | _, _ => .error (.malformed "bad classical parity assignment")
        else .error (.malformed "expected 'xor' after ':='")
    | _ =>
      let push (r : Except ParseError Gate) : Except ParseError (List Gate) := do let g ← r; .ok (g :: acc)
      if      head == "Prep0" then push (oneQ .prepZero rest)
      else if head == "Prep"  then                    -- 'Prep+'
        match rest with
        | '+' :: q => push (oneQ .prepPlus q)
        | _ => .error (.malformed "expected 'Prep0' or 'Prep+'")
      else if head == "H" then push (oneQ .H rest)
      else if head == "S" then push (oneQ .S rest)
      else if head == "X" then push (oneQ .X rest)
      else if head == "Z" then push (oneQ .Z rest)
      else if head == "CNOT" then push (twoQ .CNOT rest)
      else if head == "CZ"   then push (twoQ .CZ rest)
      else if head == "Meas" then
        match spanArrow rest with
        | some (lhs, rhs) =>
            match parseTaggedNat? 'q' lhs, parseTaggedNat? 'c' rhs with
            | some q, some r => .ok (.meas q r :: acc)
            | _, _ => .error (.malformed "bad 'Meas q -> c'")
        | none => .error (.malformed "expected 'Meas q -> c'")
      else if head == "If" then
        match (splitOnChar ' ' rest).filter (fun t => ! (trimL t).isEmpty) with
        | [rt, th, pt, qt] =>
            if String.ofList (trimL th) == "then" then
              match parseTaggedNat? 'c' rt, parseTaggedNat? 'q' qt with
              | some r, some q => .ok (.ifPauli r (pauliOf pt) q :: acc)
              | _, _ => .error (.malformed "bad 'If r then P q'")
            else .error (.malformed "expected 'then' in 'If r then P q'")
        | _ => .error (.malformed "expected 'If r then P q'")
      else .error (.unknownStatement (String.ofList s))

/-- **Parse QClifford text to a `QClifford.Circuit`.** -/
def parseQClifford (src : String) : Except ParseError Circuit :=
  match (stmtSegments src).foldlM parseGate [] with
  | .ok rev  => .ok rev.reverse
  | .error e => .error e

/-! ## Tests — `by decide`. -/

/-- `src` parses to exactly `circ`. -/
def parsesTo (src : String) (circ : Circuit) : Bool :=
  match parseQClifford src with
  | .ok c    => decide (c = circ)
  | .error _ => false

-- `CNOT(0,1)` realized from a `CZ` parses to exactly `QClifford.cnotFromCZ 0 1`:
example : parsesTo "H q1\nCZ q0 q1\nH q1" (cnotFromCZ 0 1) = true := by decide

-- the standard-Z syndrome extraction (§12 machine form) parses exactly:
example : parsesTo "Prep0 q3\nCNOT q1 q3\nCNOT q0 q3\nMeas q3 -> c7"
    [.prepZero 3, .CNOT 1 3, .CNOT 0 3, .meas 3 7] = true := by decide

-- prep+, classical parity, comma operands, and a conditioned Pauli all parse:
example : parsesTo "Prep+ q2; c5 := xor c0 c1; If c2 then X q0"
    [.prepPlus 2, .parity 5 [0, 1], .ifPauli 2 .X 0] = true := by decide

-- bare (untagged) qubit/cbit numbers parse the same:
example : parsesTo "H 1; Meas 1 -> 0" [.H 1, .meas 1 0] = true := by decide

-- an unknown gate is a structured error:
example : (match parseQClifford "Frobnicate q0" with | .error (.unknownStatement _) => true | _ => false) = true := by decide

end QClifford.Parse
