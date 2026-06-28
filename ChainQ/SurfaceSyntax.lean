/-
  ChainQ.SurfaceSyntax -- readable ChainQ source commands.

  This file gives ChainQ a small surface syntax for paper-facing code-family
  declarations.  The commands elaborate to `NamedCodeDecl`, and `check?` remains
  the checked boundary into `CheckedCSSCode`.
-/
import ChainQ.Syntax

namespace ChainQ.SurfaceSyntax

/-! ## Polynomial sugar used by code-family declarations. -/

class XVar (α : Type) where
  x : α

class YVar (α : Type) where
  y : α

def x {α : Type} [XVar α] : α := XVar.x
def y {α : Type} [YVar α] : α := YVar.y

def flatMap {α β : Type} : List α -> (α -> List β) -> List β
  | [], _ => []
  | x :: xs, f => f x ++ flatMap xs f

/-- Bivariate GF(2) polynomial syntax for BB codes. -/
structure BBPoly where
  terms : List (Nat × Nat)
  deriving Repr

namespace BBPoly

def zero : BBPoly := { terms := [] }
def one : BBPoly := { terms := [(0, 0)] }
def xVar : BBPoly := { terms := [(1, 0)] }
def yVar : BBPoly := { terms := [(0, 1)] }

def add (p q : BBPoly) : BBPoly := { terms := p.terms ++ q.terms }

def mul (p q : BBPoly) : BBPoly :=
  { terms := flatMap p.terms (fun a => q.terms.map (fun b => (a.1 + b.1, a.2 + b.2))) }

def pow : BBPoly -> Nat -> BBPoly
  | _, 0 => one
  | p, n + 1 => mul (pow p n) p

def toTerms (p : BBPoly) : List (Nat × Nat) := p.terms

instance : XVar BBPoly where x := xVar
instance : YVar BBPoly where y := yVar
instance (n : Nat) : OfNat BBPoly n where
  ofNat := if n % 2 == 0 then zero else one
instance : HAdd BBPoly BBPoly BBPoly where hAdd := add
instance : HMul BBPoly BBPoly BBPoly where hMul := mul
instance : Pow BBPoly Nat where pow := pow

end BBPoly

/-- Univariate GF(2) polynomial syntax for lifted-product circulants. -/
structure CircPoly where
  terms : List Nat
  deriving Repr

namespace CircPoly

def zero : CircPoly := { terms := [] }
def one : CircPoly := { terms := [0] }
def xVar : CircPoly := { terms := [1] }

def add (p q : CircPoly) : CircPoly := { terms := p.terms ++ q.terms }

def mul (p q : CircPoly) : CircPoly :=
  { terms := flatMap p.terms (fun a => q.terms.map (fun b => a + b)) }

def pow : CircPoly -> Nat -> CircPoly
  | _, 0 => one
  | p, n + 1 => mul (pow p n) p

def toCirc (p : CircPoly) : ChainQ.GF2.Circ := p.terms
def matrixToCirc (A : List (List CircPoly)) : List (List ChainQ.GF2.Circ) :=
  A.map (fun row => row.map toCirc)

instance : XVar CircPoly where x := xVar
instance (n : Nat) : OfNat CircPoly n where
  ofNat := if n % 2 == 0 then zero else one
instance : HAdd CircPoly CircPoly CircPoly where hAdd := add
instance : HMul CircPoly CircPoly CircPoly where hMul := mul
instance : Pow CircPoly Nat where pow := pow

end CircPoly

end ChainQ.SurfaceSyntax

open Lean Macro

private def requireFieldName (got : TSyntax `ident) (expected : Name) : MacroM Unit := do
  unless got.getId == expected do
    Macro.throwErrorAt got ("expected field `" ++ expected.toString ++ "`")

/-- Preferred user-facing indexed CSS declaration: logical qubits are supplied as
    per-qubit records, avoiding parallel name/Z/X arrays.

    Field labels are parsed as identifiers and checked in the macro rather than
    registered as Lean keywords.  This lets users write `n = ...` without making
    `n` unusable as an ordinary structure-field name elsewhere. -/
macro "indexed_css" cname:ident "{"
    nkey:ident "=" nval:term ";"
    hxkey:ident "=" hxval:term ";"
    hzkey:ident "=" hzval:term ";"
    qubitskey:ident "=" qubitsval:term ";"
  "}" : command => do
  requireFieldName nkey `n
  requireFieldName hxkey `hx
  requireFieldName hzkey `hz
  requireFieldName qubitskey `qubits
  let nameLit := Syntax.mkStrLit cname.getId.toString
  `(def $cname : ChainQ.NamedCodeDecl :=
      { name := $nameLit,
        decl := ChainQ.CodeDecl.css
          { n := $nval,
            hx := (($hxval : ChainQ.GF2.BoolMat)),
            hz := (($hzval : ChainQ.GF2.BoolMat)) },
        logicalIndex := some
          (ChainQ.LogicalIndexSpec.ofQubits
            (($qubitsval : List ChainQ.LogicalQubitSpec))) })

/-- ChainQ source command for BB declarations with checked paper parameters. -/
macro "code" name:ident "as" "BivariateBicycle" "{"
    lkey:ident "=" l:term ";"
    mkey:ident "=" m:term ";"
    akey:ident "=" A:term ";"
    bkey:ident "=" B:term ";"
    "params" "=" "(" n:num "," k:num "," d:num ")" ";"
  "}" : command => do
  requireFieldName lkey `l
  requireFieldName mkey `m
  requireFieldName akey `A
  requireFieldName bkey `B
  let nameLit := Syntax.mkStrLit name.getId.toString
  `(def $name : ChainQ.NamedCodeDecl :=
      { name := $nameLit,
        decl := ChainQ.CodeDecl.bb $l $m
          (ChainQ.SurfaceSyntax.BBPoly.toTerms (($A : ChainQ.SurfaceSyntax.BBPoly)))
          (ChainQ.SurfaceSyntax.BBPoly.toTerms (($B : ChainQ.SurfaceSyntax.BBPoly))),
        claimedParams := some ({ n := $n, k := $k, d := $d } : ChainQ.CodeParamClaim),
        distanceProfile := ChainQ.knownPaperTableProfileByParams? $n $k $d })

/-- BB declaration with an explicit user logical-qubit index. -/
macro "indexed_code" iname:ident "as" "BivariateBicycle" "{"
    lkey:ident "=" lval:term ";"
    mkey:ident "=" mval:term ";"
    akey:ident "=" aval:term ";"
    bkey:ident "=" bval:term ";"
    "params" "=" "(" nval:num "," kval:num "," dval:num ")" ";"
    "logicals" "=" "(" lnames:term "," lbasis:term ")" ";"
  "}" : command => do
  requireFieldName lkey `l
  requireFieldName mkey `m
  requireFieldName akey `A
  requireFieldName bkey `B
  let nameLit := Syntax.mkStrLit iname.getId.toString
  `(def $iname : ChainQ.NamedCodeDecl :=
      { name := $nameLit,
        decl := ChainQ.CodeDecl.bb $lval $mval
          (ChainQ.SurfaceSyntax.BBPoly.toTerms (($aval : ChainQ.SurfaceSyntax.BBPoly)))
          (ChainQ.SurfaceSyntax.BBPoly.toTerms (($bval : ChainQ.SurfaceSyntax.BBPoly))),
        claimedParams := some ({ n := $nval, k := $kval, d := $dval } : ChainQ.CodeParamClaim),
        distanceProfile := ChainQ.knownPaperTableProfileByParams? $nval $kval $dval,
        logicalIndex := some
          ({ names := (($lnames : List String)),
             pauliBasis :=
              { zBasis := (($lbasis : ChainQ.CSSLogicalBasis)).lz,
                xDualBasis := (($lbasis : ChainQ.CSSLogicalBasis)).lx } } :
            ChainQ.LogicalIndexSpec) })

/-- ChainQ source command for lifted-product declarations with checked paper parameters. -/
macro "code" name:ident "as" "LiftedProduct" "{"
    ellkey:ident "=" ell:term ";"
    rowskey:ident "=" rows:term ";"
    colskey:ident "=" cols:term ";"
    protokey:ident "=" protograph:term ";"
    "params" "=" "(" n:num "," k:num "," d:num ")" ";"
  "}" : command => do
  requireFieldName ellkey `ell
  requireFieldName rowskey `rows
  requireFieldName colskey `cols
  requireFieldName protokey `protograph
  let nameLit := Syntax.mkStrLit name.getId.toString
  `(def $name : ChainQ.NamedCodeDecl :=
      { name := $nameLit,
        decl := ChainQ.CodeDecl.liftedProduct $ell
          (ChainQ.SurfaceSyntax.CircPoly.matrixToCirc
            (($protograph : List (List ChainQ.SurfaceSyntax.CircPoly))))
          $rows $cols,
        claimedParams := some ({ n := $n, k := $k, d := $d } : ChainQ.CodeParamClaim),
        distanceProfile := ChainQ.knownPaperTableProfileByParams? $n $k $d })

/-- Lifted-product declaration with an explicit user logical-qubit index. -/
macro "indexed_code" iname:ident "as" "LiftedProduct" "{"
    ellkey:ident "=" ellval:term ";"
    rowskey:ident "=" rowsval:term ";"
    colskey:ident "=" colsval:term ";"
    protokey:ident "=" protoval:term ";"
    "params" "=" "(" nval:num "," kval:num "," dval:num ")" ";"
    "logicals" "=" "(" lnames:term "," lbasis:term ")" ";"
  "}" : command => do
  requireFieldName ellkey `ell
  requireFieldName rowskey `rows
  requireFieldName colskey `cols
  requireFieldName protokey `protograph
  let nameLit := Syntax.mkStrLit iname.getId.toString
  `(def $iname : ChainQ.NamedCodeDecl :=
      { name := $nameLit,
        decl := ChainQ.CodeDecl.liftedProduct $ellval
          (ChainQ.SurfaceSyntax.CircPoly.matrixToCirc
            (($protoval : List (List ChainQ.SurfaceSyntax.CircPoly))))
          $rowsval $colsval,
        claimedParams := some ({ n := $nval, k := $kval, d := $dval } : ChainQ.CodeParamClaim),
        distanceProfile := ChainQ.knownPaperTableProfileByParams? $nval $kval $dval,
        logicalIndex := some
          ({ names := (($lnames : List String)),
             pauliBasis :=
              { zBasis := (($lbasis : ChainQ.CSSLogicalBasis)).lz,
                xDualBasis := (($lbasis : ChainQ.CSSLogicalBasis)).lx } } :
            ChainQ.LogicalIndexSpec) })

indexed_code indexedTinyLPFromSyntax as LiftedProduct {
  ell = 1;
  rows = 1;
  cols = 1;
  protograph = [[1]];
  params = (2, 0, 1);
  logicals = ([], { lx := [], lz := [] });
}

example :
    (match indexedTinyLPFromSyntax.logicalIndex with
     | some spec => spec.names = []
     | none => false) = true := by decide

indexed_css indexedToyLP3Syntax {
  n = 6;
  hx = (ChainQ.toyLPCSS 3).hx;
  hz = (ChainQ.toyLPCSS 3).hz;
  qubits = ChainQ.toyLPQubitSpecs;
}

example : ChainQ.isOk indexedToyLP3Syntax.checkLogicalIndex? = true := by decide

def badSurfaceNotCycleQubits : List ChainQ.LogicalQubitSpec :=
  [ { name := "bad_z", z := ChainQ.unitVec 3 0 ++ ChainQ.zeros 3, x := ChainQ.toyLPX1 3 },
    { name := "bridge_ab", z := ChainQ.toyLPZ2 3, x := ChainQ.toyLPX2 3 } ]

indexed_css badSurfaceNotCycleDecl {
  n = 6;
  hx = (ChainQ.toyLPCSS 3).hx;
  hz = (ChainQ.toyLPCSS 3).hz;
  qubits = badSurfaceNotCycleQubits;
}

example : ChainQ.isOk badSurfaceNotCycleDecl.checkLogicalIndex? = false := by decide

def badSurfaceBoundaryQubits : List ChainQ.LogicalQubitSpec :=
  [ { name := "stab_z", z := (ChainQ.toyLPCSS 3).hz.getD 0 [], x := ChainQ.toyLPX1 3 },
    { name := "bridge_ab", z := ChainQ.toyLPZ2 3, x := ChainQ.toyLPX2 3 } ]

indexed_css badSurfaceBoundaryDecl {
  n = 6;
  hx = (ChainQ.toyLPCSS 3).hx;
  hz = (ChainQ.toyLPCSS 3).hz;
  qubits = badSurfaceBoundaryQubits;
}

example : ChainQ.isOk badSurfaceBoundaryDecl.checkLogicalIndex? = false := by decide

def badSurfaceCosetQubits : List ChainQ.LogicalQubitSpec :=
  [ { name := "global_a", z := ChainQ.toyLPZ1 3, x := ChainQ.toyLPX1 3 },
    { name := "same_coset", z := ChainQ.toyLPZ1PlusStab0, x := ChainQ.toyLPX2 3 } ]

indexed_css badSurfaceCosetDecl {
  n = 6;
  hx = (ChainQ.toyLPCSS 3).hx;
  hz = (ChainQ.toyLPCSS 3).hz;
  qubits = badSurfaceCosetQubits;
}

example : ChainQ.isOk badSurfaceCosetDecl.checkLogicalIndex? = false := by decide

def badSurfacePairingQubits : List ChainQ.LogicalQubitSpec :=
  [ { name := "global_a", z := ChainQ.toyLPZ1 3, x := ChainQ.toyLPX2 3 },
    { name := "bridge_ab", z := ChainQ.toyLPZ2 3, x := ChainQ.toyLPX1 3 } ]

indexed_css badSurfacePairingDecl {
  n = 6;
  hx = (ChainQ.toyLPCSS 3).hx;
  hz = (ChainQ.toyLPCSS 3).hz;
  qubits = badSurfacePairingQubits;
}

example : ChainQ.isOk badSurfacePairingDecl.checkLogicalIndex? = false := by decide
