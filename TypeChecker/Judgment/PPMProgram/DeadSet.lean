/-
  TypeChecker.Judgment.PPMProgram.DeadSet — a normalized finite-set of logical
  qubits (Mathlib-free) with set operations and their basic lemmas.
-/
import TypeChecker.Judgment.PPM

namespace TypeChecker
open ChainQ.GF2 Logical PPM

/-! ## A normalized finite-set of logical qubits (Mathlib-free).

    `DeadSet` is a duplicate-free list of logical qubits with set operations:
    `insert` dedups, `union` is set union (not list append), `subset` is the
    set order.  Branch joins use `union`; the loop "discards nothing" test uses
    `subset` (since discards only grow the set). -/
abbrev DeadSet := List LQubit

/-- Membership. -/
def DeadSet.mem (s : DeadSet) (q : LQubit) : Bool := s.contains q
/-- Insert (deduplicating). -/
def DeadSet.insert (q : LQubit) (s : DeadSet) : DeadSet := if s.contains q then s else q :: s
/-- Set union (insert every element of `a` into `b`). -/
def DeadSet.union (a b : DeadSet) : DeadSet := a.foldr DeadSet.insert b
/-- Set inclusion. -/
def DeadSet.subset (a b : DeadSet) : Bool := a.all (fun q => b.contains q)
/-- Does the set contain ANY logical qubit of block `blk`? -/
def DeadSet.hasBlock (blk : Nat) (s : DeadSet) : Bool := s.any (fun q => q.blk == blk)

/-- `insert q` always contains `q`. -/
theorem DeadSet.contains_insert_self {s : DeadSet} {q : LQubit} :
    (DeadSet.insert q s).contains q = true := by
  unfold DeadSet.insert; split
  · assumption
  · simp

/-- `insert` preserves membership. -/
theorem DeadSet.contains_insert_of_contains {s : DeadSet} {q q' : LQubit}
    (h : s.contains q = true) : (DeadSet.insert q' s).contains q = true := by
  unfold DeadSet.insert; split
  · exact h
  · rw [List.contains_cons, h, Bool.or_true]

/-- If no dead qubit lies in block `b`, searching the dead set for block `b`
    finds nothing (the resource precondition the mixed checker uses). -/
theorem DeadSet.find?_eq_none_of_not_hasBlock {s : DeadSet} {b : Nat}
    (h : DeadSet.hasBlock b s = false) : s.find? (fun x => x.blk == b) = none := by
  unfold DeadSet.hasBlock at h
  induction s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    obtain ⟨hx, hxs⟩ := h
    simp only [List.find?_cons, hx]
    exact ih hxs

/-- `union` preserves left membership. -/
theorem DeadSet.contains_union_left {a b : DeadSet} {q : LQubit} :
    a.contains q = true → (DeadSet.union a b).contains q = true := by
  unfold DeadSet.union
  induction a with
  | nil => simp
  | cons x xs ih =>
    intro h
    simp only [List.foldr_cons]
    rw [List.contains_cons] at h
    cases hx : (q == x) with
    | true  => rw [eq_of_beq hx]; exact DeadSet.contains_insert_self
    | false => rw [hx, Bool.false_or] at h; exact DeadSet.contains_insert_of_contains (ih h)

end TypeChecker
