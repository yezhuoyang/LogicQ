/-
  Compiler.QStab2QClifford.Trace — the trace-host classical-dataflow foundation.

  A QClifford circuit run against `traceHost` has NO quantum state: every
  preparation / Clifford / feed-forward gate is a no-op, and a `Z`-measurement
  simply reads the next bit of an outcome trace.  So `run (traceHost outcome)`
  collapses to a PURE CLASSICAL FOLD over the measurement / parity gates —
  captured exactly by `traceFold`.

  The linchpin lemma `run_traceHost` proves `run (traceHost outcome) = traceFold`.
  Every downstream scheme then needs only to COMPUTE `traceFold` of its emitted
  circuit (no per-scheme `run` induction).  This is the classical SSA dataflow
  contract — NOT a physical stabilizer-channel or fault-tolerance claim.
-/
import QClifford.Basic

namespace Compiler.QStab2QClifford

open Physical

abbrev Circuit := QClifford.Circuit
abbrev CBit := QClifford.CBit
abbrev Store := QClifford.Store

/-- A host whose quantum operations are no-ops and whose measurements read a
    trace: the `k`-th physical measurement returns `outcome k`. -/
structure TraceState where
  next : Nat
  deriving Repr, DecidableEq

def traceHost (outcome : Nat → Bool) : QClifford.Host TraceState where
  prepZero  := fun _ st => st
  prepPlus  := fun _ st => st
  applyH    := fun _ st => st
  applyS    := fun _ st => st
  applyX    := fun _ st => st
  applyZ    := fun _ st => st
  applyCNOT := fun _ _ st => st
  applyCZ   := fun _ _ st => st
  measureZ  := fun _ st => (outcome st.next, { next := st.next + 1 })

/-- The classical-store fold a circuit induces under the trace host.  Returns the
    advanced trace cursor and the resulting store.  Every non-measurement,
    non-parity gate is a `(cursor, store)` no-op; `meas q r` reads `outcome` at
    the cursor into bit `r` and advances the cursor; `parity r srcs` writes the
    XOR of existing bits (no cursor advance). -/
def traceFold (outcome : Nat → Bool) : Circuit → Nat → Store → Nat × Store
  | [],                  k, σ => (k, σ)
  | .meas _ r :: t,      k, σ => traceFold outcome t (k + 1) (σ.set r (outcome k))
  | .parity r srcs :: t, k, σ => traceFold outcome t k (σ.set r (σ.xorOf srcs))
  | .prepZero _ :: t,    k, σ => traceFold outcome t k σ
  | .prepPlus _ :: t,    k, σ => traceFold outcome t k σ
  | .H _ :: t,           k, σ => traceFold outcome t k σ
  | .S _ :: t,           k, σ => traceFold outcome t k σ
  | .X _ :: t,           k, σ => traceFold outcome t k σ
  | .Z _ :: t,           k, σ => traceFold outcome t k σ
  | .CNOT _ _ :: t,      k, σ => traceFold outcome t k σ
  | .CZ _ _ :: t,        k, σ => traceFold outcome t k σ
  | .ifPauli _ _ _ :: t, k, σ => traceFold outcome t k σ

/-- Field-projection lemmas: reduce a single host projection of `traceHost`
    WITHOUT unfolding the bare `traceHost outcome` token elsewhere (which would
    break the induction hypothesis in `run_traceHost`). -/
@[simp] theorem traceHost_prepZero (outcome) : (traceHost outcome).prepZero = fun _ st => st := rfl
@[simp] theorem traceHost_prepPlus (outcome) : (traceHost outcome).prepPlus = fun _ st => st := rfl
@[simp] theorem traceHost_applyH (outcome) : (traceHost outcome).applyH = fun _ st => st := rfl
@[simp] theorem traceHost_applyS (outcome) : (traceHost outcome).applyS = fun _ st => st := rfl
@[simp] theorem traceHost_applyX (outcome) : (traceHost outcome).applyX = fun _ st => st := rfl
@[simp] theorem traceHost_applyZ (outcome) : (traceHost outcome).applyZ = fun _ st => st := rfl
@[simp] theorem traceHost_applyCNOT (outcome) : (traceHost outcome).applyCNOT = fun _ _ st => st := rfl
@[simp] theorem traceHost_applyCZ (outcome) : (traceHost outcome).applyCZ = fun _ _ st => st := rfl
@[simp] theorem traceHost_measureZ (outcome) :
    (traceHost outcome).measureZ = fun _ st => (outcome st.next, { next := st.next + 1 }) := rfl

/-- Under the trace host every feed-forward Pauli is a no-op. -/
@[simp] theorem traceHost_applyPauli (outcome : Nat → Bool) (p : Pauli) (q : PQubit) (st : TraceState) :
    QClifford.applyPauli (traceHost outcome) p q st = st := by
  cases p <;> simp [QClifford.applyPauli]

/-- **Linchpin**: running a circuit on the trace host equals the classical
    `traceFold`.  Reduces all subsequent run-reasoning to computing `traceFold`. -/
theorem run_traceHost (outcome : Nat → Bool) (c : Circuit) (k : Nat) (σ : Store) :
    QClifford.run (traceHost outcome) c { next := k } σ
      = ({ next := (traceFold outcome c k σ).1 }, (traceFold outcome c k σ).2) := by
  induction c generalizing k σ with
  | nil => rfl
  | cons g t ih =>
      cases g <;>
        simp only [QClifford.run, traceFold, traceHost_prepZero, traceHost_prepPlus,
          traceHost_applyH, traceHost_applyS, traceHost_applyX, traceHost_applyZ,
          traceHost_applyCNOT, traceHost_applyCZ, traceHost_measureZ, traceHost_applyPauli,
          ite_self, ih]

/-- `traceFold` distributes over `++`, threading the cursor and store. -/
theorem traceFold_append (outcome : Nat → Bool) (c₁ c₂ : Circuit) (k : Nat) (σ : Store) :
    traceFold outcome (c₁ ++ c₂) k σ
      = traceFold outcome c₂ (traceFold outcome c₁ k σ).1 (traceFold outcome c₁ k σ).2 := by
  induction c₁ generalizing k σ with
  | nil => rfl
  | cons g t ih => cases g <;> simp [traceFold, ih]

/-! ## No-op blocks.

    Circuits built only from preparations / Cliffords / CNOTs (no `meas`, no
    `parity`) leave the cursor and store untouched.  These let each scheme's
    quantum "plumbing" (cat cascades, data couplings, basis-change `H`s) drop out
    of the trace computation. -/

/-- A list of `CNOT`s (control = `anc`, varying target) is a trace no-op. -/
theorem traceFold_cnot_from (outcome : Nat → Bool) (anc : PQubit)
    (qs : List PQubit) (k : Nat) (σ : Store) :
    traceFold outcome (qs.map (fun q => QClifford.Gate.CNOT anc q)) k σ = (k, σ) := by
  induction qs generalizing k σ with
  | nil => rfl
  | cons q qs ih => simpa [traceFold] using ih k σ

/-- A list of `CNOT`s (target = `anc`, varying control) is a trace no-op. -/
theorem traceFold_cnot_to (outcome : Nat → Bool) (anc : PQubit)
    (qs : List PQubit) (k : Nat) (σ : Store) :
    traceFold outcome (qs.map (fun q => QClifford.Gate.CNOT q anc)) k σ = (k, σ) := by
  induction qs generalizing k σ with
  | nil => rfl
  | cons q qs ih => simpa [traceFold] using ih k σ

/-! ## Generic measurement loop.

    A multi-measurement scheme (Shor cat block, Knill transversal) emits, per
    element of an ordered list, some quantum "plumbing" (`body`, a trace no-op)
    followed by exactly one measurement into a consecutive fresh bit.  `measLoop`
    captures this shape and `traceFold_measLoop` computes its trace in one go. -/

/-- For each element `x` of the list, emit `body x` (quantum plumbing) then a
    measurement of `mq x` into the running fresh bit `b, b+1, …`. -/
def measLoop {α : Type} (body : α → Circuit) (mq : α → PQubit) : List α → CBit → Circuit
  | [],      _ => []
  | x :: xs, b => body x ++ QClifford.Gate.meas (mq x) b :: measLoop body mq xs (b + 1)

/-- The store after a `measLoop`: bits `b, b+1, …` hold the consecutive trace
    outcomes `outcome k, outcome (k+1), …` — one per element (qubit identities and
    plumbing are irrelevant to the classical trace). -/
def setOutcomes {α : Type} (outcome : Nat → Bool) : List α → CBit → Nat → Store → Store
  | [],      _, _, σ => σ
  | _ :: xs, b, k, σ => setOutcomes outcome xs (b + 1) (k + 1) (σ.set b (outcome k))

/-- `traceFold` of a `measLoop` advances the cursor by the number of elements and
    records each measurement's outcome into its fresh bit. -/
theorem traceFold_measLoop {α : Type} (outcome : Nat → Bool) (body : α → Circuit) (mq : α → PQubit)
    (hbody : ∀ x k σ, traceFold outcome (body x) k σ = (k, σ))
    (xs : List α) (b k : Nat) (σ : Store) :
    traceFold outcome (measLoop body mq xs b) k σ
      = (k + xs.length, setOutcomes outcome xs b k σ) := by
  induction xs generalizing b k σ with
  | nil => rfl
  | cons x xs ih =>
      rw [measLoop, traceFold_append, hbody]
      simp only [traceFold]
      rw [ih, setOutcomes, List.length_cons]
      congr 1
      omega

/-! ## No-op blocks and the uniform multi-measurement gadget.

    A multi-measurement scheme emits `plumbing ++ measGroup ms a ++ [parity v synbits]`:
    the quantum `plumbing` (preparations, cat cascade, data couplings, flag
    couplings, basis-change `H`s) is a trace no-op; `measGroup` measures each qubit
    of `ms` into a fresh consecutive bit; the final `parity` XORs the SYNDROME bits
    into the result var.  `traceFold_multiGadget` computes the whole gadget at once. -/

/-- A circuit performs no measurement and no classical parity. -/
def noMeasParity (c : Circuit) : Bool :=
  c.all (fun g => !g.isMeas && !g.isClassical)

@[simp] theorem noMeasParity_nil : noMeasParity [] = true := rfl

@[simp] theorem noMeasParity_append (c₁ c₂ : Circuit) :
    noMeasParity (c₁ ++ c₂) = (noMeasParity c₁ && noMeasParity c₂) := by
  simp [noMeasParity, List.all_append]

/-- `CNOT`s with a fixed control are never measurements/parities. -/
theorem noMeasParity_cnotFrom (anc : PQubit) (qs : List PQubit) :
    noMeasParity (qs.map (fun q => QClifford.Gate.CNOT anc q)) = true := by
  simp [noMeasParity, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

/-- `CNOT`s with a fixed target are never measurements/parities. -/
theorem noMeasParity_cnotTo (anc : PQubit) (qs : List PQubit) :
    noMeasParity (qs.map (fun q => QClifford.Gate.CNOT q anc)) = true := by
  simp [noMeasParity, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

/-- A `noMeasParity` circuit is a complete trace no-op (cursor and store unchanged). -/
theorem traceFold_noop (outcome : Nat → Bool) (c : Circuit) (h : noMeasParity c = true)
    (k : Nat) (σ : Store) :
    traceFold outcome c k σ = (k, σ) := by
  induction c generalizing k σ with
  | nil => rfl
  | cons g t ih =>
      rw [noMeasParity, List.all_cons, Bool.and_eq_true] at h
      have ht := ih h.2
      cases g <;>
        simp_all [traceFold, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

/-- Measure each qubit of `ms` into consecutive fresh bits `a, a+1, …`. -/
def measGroup (ms : List PQubit) (a : CBit) : Circuit :=
  measLoop (fun _ => []) (fun q => q) ms a

theorem traceFold_measGroup (outcome : Nat → Bool) (ms : List PQubit) (a k : Nat) (σ : Store) :
    traceFold outcome (measGroup ms a) k σ = (k + ms.length, setOutcomes outcome ms a k σ) :=
  traceFold_measLoop outcome (fun _ => []) (fun q => q) (fun _ _ _ => rfl) ms a k σ

/-- **Uniform multi-measurement gadget**: `traceFold` of `plumbing ++ measGroup ms a
    ++ [parity v synbits]` advances the cursor by `ms.length`, records each
    measurement into its fresh bit, and XORs the syndrome bits into `v`. -/
theorem traceFold_multiGadget (outcome : Nat → Bool) (plumbing : Circuit) (ms : List PQubit)
    (synbits : List CBit) (v a k : Nat) (σ : Store) (hpl : noMeasParity plumbing = true) :
    traceFold outcome (plumbing ++ measGroup ms a ++ [QClifford.Gate.parity v synbits]) k σ
      = (k + ms.length,
          (setOutcomes outcome ms a k σ).set v ((setOutcomes outcome ms a k σ).xorOf synbits)) := by
  rw [List.append_assoc, traceFold_append, traceFold_noop outcome plumbing hpl,
      traceFold_append, traceFold_measGroup]
  simp [traceFold]

end Compiler.QStab2QClifford
