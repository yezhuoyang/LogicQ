/-
  TypeChecker.Judgment.PPM.Lift — block-diagonal lifting into the merged
  symplectic space and the named merged-code certificate components.
-/
import TypeChecker.Core.Block
import TypeChecker.Core.Error
import PPM.Basic

namespace TypeChecker
open ChainQ.GF2

/-! ## Lifting into the merged symplectic space (general). -/

/-- `k` zero bits. -/
def zeros (k : Nat) : BoolVec := List.replicate k false

/-- Place a width-`ni` half (X- or Z-block) at offset `off` in a width-`mergedN`
    block. -/
def padHalf (mergedN off ni : Nat) (h : BoolVec) : BoolVec :=
  zeros off ++ h ++ zeros (mergedN - off - ni)

/-- Lift a width-`2·ni` symplectic Pauli vector to the merged width-`2·mergedN`
    space, placing the block's qubits at `[off, off+ni)`. -/
def liftSym (mergedN off ni : Nat) (v : BoolVec) : BoolVec :=
  padHalf mergedN off ni (v.take ni) ++ padHalf mergedN off ni (v.drop ni)

/-- Lift a whole stabilizer/logical matrix. -/
def liftMat (mergedN off ni : Nat) (m : BoolMat) : BoolMat := m.map (liftSym mergedN off ni)

/-- Whether `v` commutes (symplectically) with every row of `S`. -/
def commutesAllSt (n : Nat) (S : BoolMat) (v : BoolVec) : Bool :=
  S.all (fun s => !(sympForm n s v))

/-- Order-preserving de-duplication of block ids. -/
def dedupNat (l : List Nat) : List Nat :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- SAFE physical representative of a logical factor (`X̄/Z̄/Ȳ` on logical qubit
    `j` of `blk`): `none` if `j` is out of range for the block's logical basis —
    an out-of-range index is NEVER a silent zero row (uses `ChainQ.GF2.row?`). -/
def factorRep? (blk : Block) (j : Nat) (pl : PPM.PLetter) : Option BoolVec :=
  match pl with
  | .X => row? blk.lx j
  | .Z => row? blk.lz j
  | .Y => match row? blk.lx j, row? blk.lz j with
          | some x, some z => some (vecXor x z)
          | _, _           => none

/-- The representative with a zero default — used ONLY after `checkPPM`'s
    precheck has confirmed every index is in range (so the default never fires). -/
def factorRepD (blk : Block) (j : Nat) (pl : PPM.PLetter) : BoolVec :=
  (factorRep? blk j pl).getD (zeros (2 * blk.n))

/-- Gather the touched blocks with their offsets in the combined space; `none`
    if any block is unknown or not live.  Blocks come from a `TypedEnv`, so each
    is already well-formed; `gather` extracts the underlying `Block`. -/
def gather (Γ : TypedEnv) : List BlockId → Option (List (BlockId × Block × Nat) × Nat)
  | []        => some ([], 0)
  | b :: rest =>
    match Γ.block? b with
    | none => none
    | some tb =>
      let blk := tb.block
      if !blk.live then none
      else match gather Γ rest with
        | none => none
        | some (lst, nRest) =>
            some ((b, blk, 0) :: lst.map (fun t => (t.1, t.2.1, t.2.2 + blk.n)), blk.n + nRest)

/-! ## The merged-code certificate (named, so soundness can reference it). -/

/-- The block-diagonally LIFTED data stabilizers in the merged space. -/
def liftedStabOf (bos : List (BlockId × Block × Nat)) (mergedN : Nat) : BoolMat :=
  bos.flatMap (fun t => liftMat mergedN t.2.2 t.2.1.n t.2.1.stab)

/-- The merged stabilizer group: lifted data stabilizers ++ the capability's
    connection stabilizers. -/
def mergedStabOf (bos : List (BlockId × Block × Nat)) (mergedN : Nat) (connStab : BoolMat) : BoolMat :=
  liftedStabOf bos mergedN ++ connStab

/-- The target Pauli's representative, lifted into the merged space. -/
def targetPOf (bos : List (BlockId × Block × Nat)) (mergedN : Nat) (P : PPM.MTarget) : BoolVec :=
  P.foldl (fun acc f =>
    match bos.find? (fun t => t.1 == f.1.blk) with
    | some t => vecXor acc (liftSym mergedN t.2.2 t.2.1.n (factorRepD t.2.1 f.1.idx f.2))
    | none   => acc) (zeros (2 * mergedN))

end TypeChecker
