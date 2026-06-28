/-
  Compiler.CodeSwitch.QLDPCPapers.ChainQProgram

  qLDPC BB/LP paper codes written in ChainQ surface syntax.
-/
import ChainQ.SurfaceSyntax

namespace Compiler.CodeSwitch.QLDPCPaperProgram

open ChainQ.SurfaceSyntax
open ChainQ ChainQ.GF2

/-! ## Universal adapters. -/

-- BB1 from Universal Adapters: [[98,6,12]]
-- l = m = 7, A = x^3 + y^3 + y^4, B = y^6 + x^2 + x^5.
code adapterBB1Decl as BivariateBicycle {
  l = 7;
  m = 7;
  A = x^3 + y^3 + y^4;
  B = y^6 + x^2 + x^5;
  params = (98, 6, 12);
}

-- LP2 from Universal Adapters: [[200,20,10]]
-- ell = 8 and the paper's 3 x 4 protograph matrix.
code adapterLP2Decl as LiftedProduct {
  ell = 8;
  rows = 3;
  cols = 4;
  protograph =
    [[x^2, 1,   1,   x^2],
     [1,   x,   x^2, x  ],
     [x^2, x,   x^3, x^2]];
  params = (200, 20, 10);
}

/-! ## Dimension-jump BB rows. -/

-- [[18,2,3]]
code dimJumpBB18Decl as BivariateBicycle {
  l = 3;
  m = 3;
  A = x^2 * y + x^2 * y^2;
  B = 1 + x * y^2;
  params = (18, 2, 3);
}

-- [[30,2,5]]
code dimJumpBB30Decl as BivariateBicycle {
  l = 3;
  m = 5;
  A = x + y^2;
  B = 1 + x * y^2;
  params = (30, 2, 5);
}

-- [[54,2,6]]
code dimJumpBB54Decl as BivariateBicycle {
  l = 3;
  m = 9;
  A = x * y^3 + x^2 * y;
  B = 1 + x * y^8;
  params = (54, 2, 6);
}

/-! ## Lifted-toric LP rows. -/

-- [[16,2,4]]
code liftedToric16Decl as LiftedProduct {
  ell = 2;
  rows = 2;
  cols = 2;
  protograph =
    [[1, x],
     [1, 1]];
  params = (16, 2, 4);
}

-- [[36,2,6]]
code liftedToric36Decl as LiftedProduct {
  ell = 2;
  rows = 3;
  cols = 3;
  protograph =
    [[1, x, 0],
     [0, 1, 1],
     [1, 0, 1]];
  params = (36, 2, 6);
}

/-! ## Fast elaboration tests for the surface syntax. -/

def isBBDecl (d : NamedCodeDecl) (lVal mVal : Nat)
    (polyA polyB : List (Nat × Nat)) : Bool :=
  match d.decl with
  | .bb l' m' A' B' => l' == lVal && m' == mVal && A' == polyA && B' == polyB
  | _ => false

def isLPDecl (d : NamedCodeDecl) (ellVal : Nat)
    (proto : List (List Circ)) (rowCount colCount : Nat) : Bool :=
  match d.decl with
  | .liftedProduct ell' P' rows' cols' =>
      ell' == ellVal && P' == proto && rows' == rowCount && cols' == colCount
  | _ => false

example : isBBDecl adapterBB1Decl 7 7
    [(3, 0), (0, 3), (0, 4)] [(0, 6), (2, 0), (5, 0)] = true := by decide

example : isLPDecl adapterLP2Decl 8
    [[[2], [0], [0], [2]],
     [[0], [1], [2], [1]],
     [[2], [1], [3], [2]]] 3 4 = true := by decide

example : adapterLP2Decl.claimedParams = some { n := 200, k := 20, d := 10 } := by decide

example : isBBDecl dimJumpBB18Decl 3 3
    [(2, 1), (2, 2)] [(0, 0), (1, 2)] = true := by decide

example : isBBDecl dimJumpBB30Decl 3 5
    [(1, 0), (0, 2)] [(0, 0), (1, 2)] = true := by decide

example : isBBDecl dimJumpBB54Decl 3 9
    [(1, 3), (2, 1)] [(0, 0), (1, 8)] = true := by decide

example : isLPDecl liftedToric16Decl 2
    [[[0], [1]],
     [[0], [0]]] 2 2 = true := by decide

example : isLPDecl liftedToric36Decl 2
    [[[0], [1], []],
     [[], [0], [0]],
     [[0], [], [0]]] 3 3 = true := by decide

/-! ## Negative declaration-boundary test. -/

code badTinyLPDecl as LiftedProduct {
  ell = 3;
  rows = 1;
  cols = 2;
  protograph = [[1, x]];
  params = (14, 0, 1);
}

example : ChainQ.isOk badTinyLPDecl.check? = false := by decide

end Compiler.CodeSwitch.QLDPCPaperProgram
