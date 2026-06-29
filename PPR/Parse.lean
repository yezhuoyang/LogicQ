/-
  PPR.Parse — a TOTAL text parser for the Pauli-Product-Rotation IR (level L_PPR),
  realising the BNF in `PPR/Syntax.lean`:

      Pauli       ::= 'X' | 'Y' | 'Z'
      PauliString ::= (LQubit '↦' Pauli)*               -- space-separated factors
      Angle       ::= 'π' | 'π/2' | 'π/4' | 'π/8'
      Phase       ::= ('+' | '-') Angle
      Rot         ::= Phase '·' PauliString             -- exp(i φ P)
      RotProg     ::= Rot*                              -- rotations on newlines / ';'
      LQubit      ::= Block '[' Nat ']'                 -- e.g. q[0]

  Block names (`q`, `a`, …) are mapped to `Logical.BlockId`s in first-occurrence order
  (the "front end maps names to ids" map).  Text → `PPR.RotProg` (the checked AST in
  `Syntax.lean`); reuses the shared char-list lexers (`Parsing.Basic`), so the parse tests
  are `by decide`.
-/
import PPR.Syntax
import Parsing.Basic

namespace PPR.Parse
open Parsing
open Logical

set_option maxRecDepth 10000

/-- The rotation angle a token denotes. -/
def parseAngle? (cs : List Char) : Option PPR.Angle :=
  let s := String.ofList (trimL cs)
  if      s == "π"   then some .pi
  else if s == "π/2" then some .piHalf
  else if s == "π/4" then some .piQuarter
  else if s == "π/8" then some .piEighth
  else none

/-- Parse a phase `('+'|'-') Angle`. -/
def parsePhase (cs : List Char) : Except ParseError PPR.Phase :=
  match trimL cs with
  | '+' :: a => match parseAngle? a with | some ang => .ok ⟨false, ang⟩ | none => .error (.malformed "bad angle")
  | '-' :: a => match parseAngle? a with | some ang => .ok ⟨true,  ang⟩ | none => .error (.malformed "bad angle")
  | _ => .error (.malformed "phase must start with '+' or '-'")

/-- The single-qubit Pauli a factor's letter denotes (`X`/`Y`/`Z`). -/
def pauliLetter? (cs : List Char) : Option PPR.Pauli :=
  match trimL cs with
  | 'X' :: _ => some .X | 'Y' :: _ => some .Y | 'Z' :: _ => some .Z | _ => none

/-- Parse a Pauli string `(q[i] ↦ P)*` (space-separated), threading the block-name table. -/
def parsePauliString (names : List String) (rest : List Char) :
    Except ParseError (List String × PPR.PauliString) :=
  let factors := (splitOnChar ' ' rest).filter (fun t => ! (trimL t).isEmpty)
  factors.foldlM
    (fun (st : List String × PPR.PauliString) (f : List Char) =>
      match splitOnChar '↦' f with
      | [lhs, p] => do
          let (nm, idx) ← parseIndexed lhs
          match pauliLetter? p with
          | some pa => let (names', bid) := internName st.1 nm
                       .ok (names', st.2 ++ [(⟨bid, idx⟩, pa)])
          | none => .error (.malformed "expected a Pauli letter X/Y/Z")
      | _ => .error (.malformed "expected 'q[i] ↦ P'"))
    (names, [])

/-- Parse one rotation `Phase '·' PauliString`, threading the block-name table. -/
def parseRot (names : List String) (seg : List Char) :
    Except ParseError (List String × PPR.Rot) :=
  match splitOnChar '·' seg with
  | [phasePart, pauliPart] => do
      let ph ← parsePhase phasePart
      let (names', ps) ← parsePauliString names pauliPart
      .ok (names', ⟨ph, ps⟩)
  | _ => .error (.malformed "expected 'Phase · PauliString'")

/-- **Parse PPR text to a `PPR.RotProg`.** -/
def parsePPR (src : String) : Except ParseError PPR.RotProg :=
  match (stmtSegments src).foldlM
      (fun (st : List String × PPR.RotProg) (seg : List Char) => do
        let (names', r) ← parseRot st.1 seg
        .ok (names', st.2 ++ [r]))
      ([], []) with
  | .ok (_, rots) => .ok rots
  | .error e      => .error e

/-! ## Tests — `by decide`. -/

/-- `src` parses to exactly `prog`. -/
def parsesTo (src : String) (prog : PPR.RotProg) : Bool :=
  match parsePPR src with
  | .ok p    => decide (p = prog)
  | .error _ => false

-- a single T rotation parses to exactly `PPR.rotT ⟨0,0⟩`:
example : parsesTo "+π/8 · q[0]↦Z" [PPR.rotT ⟨0, 0⟩] = true := by decide

-- T, S, and a two-qubit ZZ rotation — same program as the README §6 (T-count 2):
def progSrc : String := "+π/8 · q[0]↦Z\n+π/4 · q[0]↦Z\n+π/8 · q[0]↦Z q[1]↦Z"
example : parsesTo progSrc [PPR.rotT ⟨0, 0⟩, PPR.rotS ⟨0, 0⟩, PPR.rotZZ ⟨0, 0⟩ ⟨0, 1⟩] = true := by decide
example : (match parsePPR progSrc with | .ok p => p.tCount | .error _ => 0) = 2 := by decide

-- a second block name interns to id 1 (first-occurrence order):
example : parsesTo "-π/4 · a[0]↦X" [⟨⟨true, .piQuarter⟩, [(⟨0, 0⟩, .X)]⟩] = true := by decide
example : parsesTo "+π/8 · q[0]↦Z a[0]↦Z" [⟨⟨false, .piEighth⟩, [(⟨0, 0⟩, .Z), (⟨1, 0⟩, .Z)]⟩] = true := by decide

-- a missing sign is a structured error:
example : (match parsePPR "π/8 · q[0]↦Z" with | .error (.malformed _) => true | _ => false) = true := by decide

end PPR.Parse
