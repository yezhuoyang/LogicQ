/-
  TypeChecker.Judgment.Transversal.Check — the logical-automorphism checker,
  the internal transversal-map builder, and the transversal checker.
-/
import TypeChecker.Judgment.Transversal.Cert
import TypeChecker.Core.Block
import TypeChecker.Core.Error

namespace TypeChecker
open ChainQ ChainQ.GF2

/-- **MILESTONE 1 (general).**  Check that an arbitrary symplectic action `M`
    (`2n×2n`) is a legal logical operation (code automorphism) on block `b` of a
    TYPED environment: `M` is `2n×2n`; `M` preserves `J`; `M` maps every
    stabilizer back into the code.  The block's well-formedness is GUARANTEED by
    `TypedEnv` (no `Block.valid` recheck).  Returns the induced logical map. -/
def checkLogicalAutomorphism (Γ : TypedEnv) (b : BlockId) (M : BoolMat) :
    Except TypeError TypedAutomorphism :=
  match Γ.block? b with
  | none => .error (.badBlock b)
  | some tb =>
    let blk := tb.block
    if !blk.live then
      .error .notLive
    else if !(decide (M.length = 2 * blk.n) && M.all (fun r => decide (r.length = 2 * blk.n))) then
      .error (.shapeMismatch "logical-automorphism action must be 2n×2n")
    else if !preservesSymp blk.n M then
      .error .notSymplectic
    else if !((applyMap blk.n M blk.stab).all (fun r => inSpan blk.stab r)) then
      .error .stabilizerNotPreserved
    else
      .ok { block     := b
            map       := M
            inducedLX := applyMap blk.n M blk.lx
            inducedLZ := applyMap blk.n M blk.lz }

/-- ⚠ INTERNAL (shape-unchecked builder).  The `2n×2n` symplectic action of a
    UNIFORM transversal single-qubit gate `g` (a `2×2` symplectic) applied to every
    qubit, in `(X-block ++ Z-block)` layout:
    `M[i][i]=g₀₀, M[i][i+n]=g₀₁, M[i+n][i]=g₁₀, M[i+n][i+n]=g₁₁`.  (So transversal
    `H` gives `J n`.)  Built by `checkTransversal`; not for direct language use. -/
def Internal.transversalMap (n : Nat) (g : BoolMat) : BoolMat :=
  let g00 := (g.getD 0 []).getD 0 false
  let g01 := (g.getD 0 []).getD 1 false
  let g10 := (g.getD 1 []).getD 0 false
  let g11 := (g.getD 1 []).getD 1 false
  ((List.range n).map (fun i => (List.range (2 * n)).map (fun j =>
      (decide (j = i) && g00) || (decide (j = i + n) && g01)))) ++
  ((List.range n).map (fun i => (List.range (2 * n)).map (fun j =>
      (decide (j = i) && g10) || (decide (j = i + n) && g11))))

/-- **MILESTONE 1 (transversal).**  Check that the UNIFORM transversal gate given
    by single-qubit symplectic `g` (`2×2`) is a legal logical operation on `b`:
    `g` is `2×2` symplectic, and its tensor power `transversalMap n g` is a code
    automorphism (reusing the general check on the locally-built action). -/
def checkTransversal (Γ : TypedEnv) (b : BlockId) (g : BoolMat) :
    Except TypeError TypedTransversal :=
  match Γ.block? b with
  | none => .error (.badBlock b)
  | some tb =>
    let blk := tb.block
    if !blk.live then
      .error .notLive
    else if !(decide (g.length = 2) && g.all (fun r => decide (r.length = 2))) then
      .error (.shapeMismatch "transversal single-qubit gate must be 2×2")
    else if !preservesSymp 1 g then
      .error .notSymplectic
    else
      let M := Internal.transversalMap blk.n g
      if !preservesSymp blk.n M then
        .error .notSymplectic
      else if !((applyMap blk.n M blk.stab).all (fun r => inSpan blk.stab r)) then
        .error .stabilizerNotPreserved
      else
        .ok { block     := b
              gate      := g
              map       := M
              inducedLX := applyMap blk.n M blk.lx
              inducedLZ := applyMap blk.n M blk.lz }

end TypeChecker
