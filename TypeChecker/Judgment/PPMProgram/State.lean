/-
  TypeChecker.Judgment.PPMProgram.State — the abstract program state `PPMState`
  and logical-qubit validity.
-/
import TypeChecker.Judgment.PPMProgram.DeadSet

namespace TypeChecker
open ChainQ.GF2 Logical PPM

/-- The abstract program state: classical outcomes bound so far, and the
    (normalized) set of logical qubits already discarded/consumed. -/
structure PPMState where
  bound : List CVar
  dead  : DeadSet
  deriving Repr, Inhabited

/-- The initial state: nothing bound, nothing discarded. -/
def PPMState.init : PPMState := ⟨[], []⟩

/-- A logical qubit `q` is valid in `Γ`: its block exists, is LIVE, and its index
    is within the block's logical dimension `k = lx.length`.  (Liveness keeps
    `frame`/`discard` consistent with `meas`, which rejects dead blocks.) -/
def validLQubit (Γ : TypedEnv) (q : LQubit) : Bool :=
  match Γ.block? q.blk with
  | some tb => tb.block.live && decide (q.idx < tb.block.lx.length)
  | none    => false

end TypeChecker
