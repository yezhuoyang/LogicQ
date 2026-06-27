/-
  ChainQ.ChainComplex — the CHAIN-COMPLEX TYPE SYSTEM of LogicQ.

  This is the front end's distinguishing feature: a QEC code is declared as a
  chain complex over Z2, and *well-typedness* is the chain-complex law
  `∂₁ ∘ ∂₂ = 0`.  The headline theorem `chainComplex_css` proves that this law
  holds **iff** the elaborated CSS code satisfies the CSS commutation
  condition `H_X · H_Zᵀ = 0` — i.e. the type system is SOUND: a well-typed
  chain complex always elaborates to a genuine (commuting) CSS code.

  A two-step complex   C₂ --∂₂--> C₁ --∂₁--> C₀   over Z2.  Qubits live on the
  1-cells (C₁).  Following the README's surface-code declaration:

      css { hx = matrix(d2); hz = transpose(matrix(d1)); }

  boundary maps are given as incidence matrices:
    d2 : (#2-cells) × (#1-cells)   row f lists the 1-cells in ∂(face f)
    d1 : (#1-cells) × (#0-cells)   row e lists the 0-cells in ∂(edge e)

  Then ∂₁∘∂₂ as a Z2 map C₂ → C₀ has matrix `d2 · d1`, and the chain law is
  `d2 · d1 = 0`.  Since hx = d2 and hz = (d1)ᵀ, we have hx·hzᵀ = d2·d1, so the
  two conditions coincide (proved below).

  Mathlib-free; the worked surface patches type-check by `decide`.

  BNF (the surface this structure denotes):
    CodeKind  ::= 'CellComplex' 'over' 'Z2'
    CellBody  ::= 'cells' '{' CellGroup* '}' 'boundary' '{' BdyEqn* '}'
                  'css' '{' 'hx' '=' MatExpr ';' 'hz' '=' MatExpr ';' '}'
    BdyEqn    ::= ('d2'|'d1') '(' CellRef ')' '=' BdySum ';'
    BdySum    ::= CellRef ('+' CellRef)*           -- formal Z2 sum
    MatExpr   ::= 'matrix' '(' ('d2'|'d1') ')' | 'transpose' '(' MatExpr ')'
-/
import ChainQ.Algebra.GF2
import ChainQ.Algebra.Shape
import ChainQ.Core.Code

namespace ChainQ
open ChainQ.GF2

/-! ## §1. The chain-complex code type. -/

/-- A two-step chain complex over Z2: `C₂ --∂₂--> C₁ --∂₁--> C₀`.
    Boundary maps are incidence matrices; qubits live on the 1-cells. -/
structure ChainComplex where
  /-- number of 2-cells (X-checks live here) -/
  nFaces : Nat
  /-- number of 1-cells (= number of qubits) -/
  nEdges : Nat
  /-- number of 0-cells (Z-checks live here) -/
  nVerts : Nat
  /-- `∂₂` as a `nFaces × nEdges` incidence matrix -/
  d2 : BoolMat
  /-- `∂₁` as a `nEdges × nVerts` incidence matrix -/
  d1 : BoolMat
  deriving Repr, Inhabited

/-- Shape well-formedness: the boundary matrices have the declared dimensions,
    using the explicit `hasShape` predicate (`∂₂` is `nFaces × nEdges`, `∂₁` is
    `nEdges × nVerts`).  A ragged matrix is rejected. -/
def ChainComplex.wellShaped (cc : ChainComplex) : Bool :=
  hasShape cc.d2 cc.nFaces cc.nEdges && hasShape cc.d1 cc.nEdges cc.nVerts

/-- **The chain-complex law** `∂₁ ∘ ∂₂ = 0` over Z2, as the honest GF(2)
    matrix product `d2 · d1 = 0`.  This is the front-end TYPING JUDGEMENT. -/
def ChainComplex.chainLaw (cc : ChainComplex) : Bool :=
  isZeroMat (matMul cc.d2 cc.d1 cc.nVerts)

/-- A chain complex is **well-typed** iff it is well-shaped and satisfies the
    chain-complex law. -/
def ChainComplex.valid (cc : ChainComplex) : Bool :=
  cc.wellShaped && cc.chainLaw

/-! ## §2. Elaboration to the CSS pivot. -/

/-- `css { hx = matrix(d2); hz = transpose(matrix(d1)); }` — elaborate the
    chain complex to its CSS check-matrix pair.  Qubits = 1-cells. -/
def ChainComplex.toCSS (cc : ChainComplex) : CSSCode :=
  { n := cc.nEdges, hx := cc.d2, hz := transpose cc.d1 cc.nVerts }

/-! ## §3. Soundness of the type system. -/

/-- **Type-system soundness.**  The chain-complex law `∂₁∘∂₂ = 0` holds iff the
    elaborated CSS code satisfies the CSS commutation condition `H_X·H_Zᵀ = 0`.
    Equivalently: every well-typed chain complex elaborates to a genuine,
    pairwise-commuting CSS code. -/
theorem chainComplex_css (cc : ChainComplex) :
    cc.chainLaw = cc.toCSS.cssCondition := by
  unfold ChainComplex.chainLaw ChainComplex.toCSS CSSCode.cssCondition matMul
  exact zero_gemmT_iff_orthogonal cc.d2 (transpose cc.d1 cc.nVerts)

/-- Corollary: a well-typed (well-shaped + chain-law) complex elaborates to a
    code that passes the CSS commutation check. -/
theorem chainComplex_toCSS_cssCondition (cc : ChainComplex)
    (h : cc.chainLaw = true) : cc.toCSS.cssCondition = true := by
  rw [← chainComplex_css]; exact h

/-! ## §4. Worked surface patches (type-check by `decide`). -/

/-- A triangle: 1 face, 3 edges, 3 vertices.
    `∂(face) = e₀ + e₁ + e₂`; `∂e₀ = v₀+v₁`, `∂e₁ = v₁+v₂`, `∂e₂ = v₂+v₀`.
    Every vertex bounds exactly two of the face's edges ⇒ `∂∂ = 0`. -/
def triangle : ChainComplex :=
  { nFaces := 1, nEdges := 3, nVerts := 3,
    d2 := [[true, true, true]],
    d1 := [[true, true, false], [false, true, true], [true, false, true]] }

example : triangle.wellShaped = true := by decide
example : triangle.chainLaw = true := by decide          -- ∂₁∘∂₂ = 0
example : triangle.valid = true := by decide
example : triangle.toCSS.cssCondition = true := by decide -- ⇒ valid CSS code
example : triangle.toCSS.n = 3 := by decide
example : triangle.toCSS.hx = [[true, true, true]] := by decide  -- one X-check: XXX

/-- A square plaquette: 1 face, 4 edges, 4 vertices (a 4-cycle).
    `∂(face) = e₀+e₁+e₂+e₃`; consecutive edges share vertices ⇒ `∂∂ = 0`.
    This is the smallest surface-code plaquette: hx = one `XXXX` check. -/
def square : ChainComplex :=
  { nFaces := 1, nEdges := 4, nVerts := 4,
    d2 := [[true, true, true, true]],
    d1 := [[true, true, false, false], [false, true, true, false],
           [false, false, true, true], [true, false, false, true]] }

example : square.wellShaped = true := by decide
example : square.chainLaw = true := by decide
example : square.toCSS.cssCondition = true := by decide
example : square.toCSS.n = 4 := by decide

/-- A NON-example: a "complex" whose boundary maps do NOT compose to zero is
    rejected by the type system (and its CSS elaboration is non-commuting),
    witnessing that `chainComplex_css` is not vacuous. -/
def broken : ChainComplex :=
  { nFaces := 1, nEdges := 2, nVerts := 2,
    d2 := [[true, true]],
    d1 := [[true, false], [false, true]] }   -- ∂(face)=e0+e1, ∂e0=v0, ∂e1=v1 ⇒ ∂∂ = v0+v1 ≠ 0

example : broken.chainLaw = false := by decide
example : broken.toCSS.cssCondition = false := by decide

end ChainQ
