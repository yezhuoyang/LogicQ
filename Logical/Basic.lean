/-
  Logical — the shared LOGICAL-computation vocabulary.

  The front end (ChainQ) declares logical blocks (`surface q1 [n,k,d]`, …); the
  logical IRs (PPR, PPM) compute on the LOGICAL QUBITS of those blocks.  This
  module fixes that shared addressing so every logical level refers to the same
  `LQubit` — there are no physical qubits at the logical level (those appear
  only after lowering to QStab / QClifford).

  Mathlib-free (pure `Nat` data).
-/

namespace Logical

/-- Identifier of a logical block — a declared code patch such as
    `surface q1 [n,k,d]`.  The front end maps block names (`q1`, `q2`, `t0`) to
    ids; here a block is just its index. -/
abbrev BlockId := Nat

/-- A **logical qubit**: the `idx`-th logical qubit of logical block `blk`
    (`0 ≤ idx < k_blk`).  Surface syntax `q1[0]` is `⟨q1, 0⟩`. -/
structure LQubit where
  blk : BlockId
  idx : Nat
  deriving DecidableEq, Repr, Inhabited

end Logical
