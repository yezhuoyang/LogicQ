/-
  TypeChecker.Core.Block — the typing environment Γ.

  A `Block` is a logical block represented over the symplectic kernel: its
  stabilizer group and logical basis are `GF2.BoolMat`s of width `2n` (no new
  code type — `CSSCode`/`StabilizerCode` elaborate in via `Symplectic`).
  Ownership/liveness (Guppy/QIR) is carried for the consume/switch milestones.
-/
import TypeChecker.Core.Symplectic
import TypeChecker.Core.Error

namespace TypeChecker
open ChainQ.GF2

/-- Ownership mode: `owned` blocks may be consumed (measured/discarded/switched);
    `borrowed` blocks may only be acted on non-destructively. -/
inductive Owned
  | owned | borrowed
  deriving DecidableEq, Repr, Inhabited

/-- A logical block: `n` physical qubits, its symplectic stabilizer generators,
    a (declared) logical basis `lx`/`lz`, and liveness/ownership state.  All
    matrices are width-`2n` symplectic `BoolMat`s. -/
structure Block where
  n    : Nat
  stab : BoolMat            -- symplectic stabilizer generator rows
  lx   : BoolMat := []      -- declared logical X̄ rows  (LogicalBasis, declared-first)
  lz   : BoolMat := []      -- declared logical Z̄ rows
  live : Bool := true
  own  : Owned := .owned
  deriving Repr

/-- **Partial** well-formedness (everything except the completeness law): every
    `stab`/`lx`/`lz` row has width `2n`; stabilizers commute; `k_X = k_Z`; logicals
    commute with stabilizers; identity symplectic pairing; no logical in the
    stabilizer span.  A `Block` exposing only SOME of its logicals satisfies this
    but NOT `Block.valid` — represent such partial exposure with `SubBlock`. -/
def Block.validPartial (b : Block) : Bool :=
  let w := 2 * b.n
  b.stab.all (fun r => decide (r.length = w)) &&
  b.lx.all (fun r => decide (r.length = w)) &&
  b.lz.all (fun r => decide (r.length = w)) &&
  sympOrthogonal b.n b.stab b.stab &&
  decide (b.lx.length = b.lz.length) &&
  sympOrthogonal b.n b.lx b.stab &&
  sympOrthogonal b.n b.lz b.stab &&
  decide (gemmT b.lx (b.lz.map (swapHalves b.n)) = identMat b.lx.length) &&
  b.lx.all (fun r => ! inSpan b.stab r) &&
  b.lz.all (fun r => ! inSpan b.stab r)

/-- A block is **well-formed and COMPLETE** (a fully-addressed logical code):
    `validPartial` AND the completeness law — the number of exposed logical pairs
    equals the code's logical dimension `k = n − rank(stab)`.  `rank` (not row
    count) is used, so REDUNDANT stabilizer generators are allowed.
    This is the symplectic analogue of `ChainQ.CSSLogicalBasis.valid` for a full
    logical basis. -/
def Block.valid (b : Block) : Bool :=
  b.validPartial &&
  decide (b.lx.length = b.n - rank b.stab)        -- COMPLETENESS: k = n − rank(stab)

/-- A block carrying a PROOF it is well-formed AND complete — the typed-core
    block.  A judgment handed a `TypedBlock` may trust all its invariants. -/
structure TypedBlock where
  block : Block
  valid : block.valid = true

/-- A **sub-block / logical view**: a block exposing only PART of its logical
    structure (gauge fragment, partially-addressed code).  It is well-formed
    (`validPartial`) but the completeness law is intentionally NOT required.  Use
    this — not `Block`/`TypedBlock` — when partial logical exposure is desired. -/
structure SubBlock where
  block : Block
  wf    : block.validPartial = true

/-- A block identifier = its index in the environment. -/
abbrev BlockId := Nat

/-- The RAW (untrusted) typing environment — the input boundary.  Blocks here may
    be malformed; validate into a `TypedEnv` before any judgment. -/
structure Env where
  blocks : List Block
  deriving Repr

/-- Look up a raw block. -/
def Env.block? (Γ : Env) (b : BlockId) : Option Block := Γ.blocks[b]?

/-- Validate one block, packaging its proof or naming it in the error. -/
def validateBlock? (i : BlockId) (b : Block) : Except TypeError TypedBlock :=
  if h : Block.valid b = true then .ok ⟨b, h⟩ else .error (.malformedBlock i)

private def ofEnvAux : List Block → Nat → Except TypeError (List TypedBlock)
  | [],        _ => .ok []
  | b :: rest, i => do
      let tb ← validateBlock? i b
      let rest' ← ofEnvAux rest (i + 1)
      return tb :: rest'

/-- The TRUSTED typing environment: every block CARRIES its validity proof, so a
    malformed block is UNREPRESENTABLE here.  Judgments consume this directly and
    never re-check `Block.valid`. -/
structure TypedEnv where
  blocks : List TypedBlock

/-- Look up a typed (validity-carrying) block. -/
def TypedEnv.block? (Γ : TypedEnv) (b : BlockId) : Option TypedBlock := Γ.blocks[b]?

/-- The raw-block entry point: validate an `Env` ONCE at the boundary; the first
    malformed block is rejected with `malformedBlock i` (its index). -/
def TypedEnv.ofEnv? (Γ : Env) : Except TypeError TypedEnv :=
  (ofEnvAux Γ.blocks 0).map TypedEnv.mk

/-! ## Smoke checks for `Block.valid` (completeness) and `TypedEnv`. -/

-- a bare logical qubit is well-formed AND complete (k = 1 − rank [] = 1):
example : Block.valid { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] } = true := by decide
-- REDUNDANT stabilizer generators are allowed (rank, not row count): XX twice ⇒ rank 1, k = 1:
example : Block.valid { n := 2, stab := [[true, true, false, false], [true, true, false, false]],
                        lx := [[true, false, false, false]], lz := [[false, false, true, true]] } = true := by decide
-- a ZERO-WIDTH logical row is rejected (width 0 ≠ 2n):
example : Block.valid { n := 1, stab := [], lx := [[]], lz := [[]] } = false := by decide
-- mismatched logical arity (k_X ≠ k_Z) is rejected:
example : Block.valid { n := 1, stab := [], lx := [[true, false]], lz := [] } = false := by decide
-- INCOMPLETE: n = 2, no stabilizers ⇒ k must be 2, but only one logical pair is exposed → invalid:
example : Block.valid { n := 2, stab := [], lx := [[true, false, false, false]],
                        lz := [[false, false, true, false]] } = false := by decide
-- …though that same block IS a legitimate `SubBlock` (partial exposure):
example : Block.validPartial { n := 2, stab := [], lx := [[true, false, false, false]],
                               lz := [[false, false, true, false]] } = true := by decide

-- a raw Env of valid blocks lifts to a TypedEnv; one with a malformed block is rejected:
example : ok? (TypedEnv.ofEnv? { blocks := [{ n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }] }) = true := by decide
example : (match TypedEnv.ofEnv? { blocks := [{ n := 1, stab := [], lx := [[]], lz := [[]] }] } with
           | .error (.malformedBlock i) => i == 0 | _ => false) = true := by decide

end TypeChecker
