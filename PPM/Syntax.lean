/-
  PPM.Syntax — the QMeas measurement-based surface language (the PPM
  level of the pipeline).  This follows the QMeas design: every primitive maps
  one-to-one to a NATIVE lattice-surgery operation (Pauli measurement,
  Pauli-frame update, destructive readout, classical control).

  LOGICAL LEVEL.  PPM (and PPR above it) operate entirely on LOGICAL qubits:
  every qubit reference is a `LQubit = ⟨block, index⟩` — the `index`-th logical
  qubit of a declared logical block (the README's `q1[0]`).  There are no bare
  physical qubits at this level; physical qubits appear only after lowering to
  QStab/QClifford.

  The distinguishing control primitive is the ADAPTIVE conditional
  `if r = +1 then S₁ else S₂`, used for outcome-dependent Pauli-frame updates
  (the byproduct corrections of measurement-based gadgets).

  Standard-PL BNF:

    Sign     ::= '+1' | '-1'
    PLetter  ::= 'X' | 'Y' | 'Z'                      -- measurement / frame axis
    LQubit   ::= Block '[' Nat ']'                    -- logical qubit q1[i]
    MTarget  ::= (LQubit '↦' PLetter)*                -- a logical Pauli product M_P(q⃗)
    Stmt  S  ::= r ':=' 'M' MTarget                   -- r := M_P(q⃗)   (Pauli measurement)
               | 'frame' PLetter '(' LQubit ')'       -- frame_X/Y/Z(q) (record byproduct)
               | 'discard' LQubit                     -- discard q
               | 'if' r '=' '+1' 'then' S 'else' S    -- adaptive conditional
               | 'for' i '=' 0 'to' N 'do' S          -- bounded loop
               | 'skip'
               | S ';' S                              -- sequencing
               | 'abort'                              -- stuck terminal (post-selection)

  This file is pure data (Mathlib-free); the small-step operational semantics
  is in `PPM/Semantics.lean`.
-/

import Logical.Basic

namespace PPM
open Logical

/-- A measurement outcome `±1`. -/
inductive Sign
  | pos   -- +1
  | neg   -- -1
  deriving DecidableEq, Repr, Inhabited

/-- A non-identity Pauli letter: the axis of a measurement factor or a
    frame byproduct. -/
inductive PLetter
  | X | Y | Z
  deriving DecidableEq, Repr, Inhabited

/-- A classical outcome variable `r` (holds a `Sign`). -/
abbrev CVar := Nat

-- Logical-qubit addressing (`BlockId`, `LQubit`) is shared vocabulary, defined
-- in `Logical` and opened above.

/-- A measurement target: a LOGICAL Pauli product over listed logical qubits.
    E.g. the joint logical measurement `M_{ZX}(q1[0], a1[0])` is
    `[(⟨q1,0⟩, .Z), (⟨a1,0⟩, .X)]`. -/
abbrev MTarget := List (LQubit × PLetter)

/-- QMeas statements. -/
inductive Stmt
  /-- `r := M_P(q⃗)` — measure the logical Pauli product `P`, binding the `±1`
      outcome to classical variable `r`. -/
  | meas    (r : CVar) (P : MTarget)
  /-- `frame_p(q)` — record a Pauli byproduct `p` on logical qubit `q`
      (classical; the frame COMPOSES, see `Semantics.lean`). -/
  | frame   (q : LQubit) (p : PLetter)
  /-- `discard q` — retire logical qubit `q`. -/
  | discard (q : LQubit)
  /-- `if r = +1 then s₁ else s₂` — the adaptive conditional on outcome `r`. -/
  | ite     (r : CVar) (s₁ s₂ : Stmt)
  /-- `for i = 0 to n do body` — bounded (statically unrollable) loop. -/
  | forLoop (n : Nat) (body : Stmt)
  /-- `skip` — the do-nothing statement. -/
  | skip
  /-- `s₁ ; s₂` — sequencing. -/
  | seq     (s₁ s₂ : Stmt)
  /-- `abort` — the stuck terminal used for post-selection / cultivation. -/
  | abort
  deriving Repr, Inhabited, DecidableEq

@[inherit_doc] infixr:60 " ;; " => Stmt.seq

/-- The QMeas measurement alphabet is restricted to single- and two-qubit
    logical Pauli observables (the natively lattice-surgery-realizable ones). -/
def MTarget.wf (P : MTarget) : Bool :=
  let qs := P.map Prod.fst
  (P.length = 1 || P.length = 2) && qs.Nodup

/-- The STRUCTURAL well-formedness of a measurement target, INDEPENDENT of weight:
    no logical qubit appears twice.  (The other structural facts — nonempty,
    in-range, live, a logical operator — are checked by `checkPPM` against the env.)
    Split out of `MTarget.wf` so a capability-backed PPM can accept HIGH-WEIGHT targets
    while native PPM stays 1- or 2-body. -/
def MTarget.noDupQubits (P : MTarget) : Bool := (P.map Prod.fst).Nodup

/-- The NATIVE-PPM arity restriction: a single- or two-qubit logical observable (the
    natively lattice-surgery-realizable weight).  High-weight targets are admitted ONLY
    through a capability whose merged-code certificate proves the target is measured. -/
def MTarget.nativeArity (P : MTarget) : Bool := P.length = 1 || P.length = 2

/-- `wf` is exactly the conjunction of the native arity restriction and structural no-dup. -/
theorem MTarget.wf_eq (P : MTarget) : P.wf = (P.nativeArity && P.noDupQubits) := rfl

/-! ## Example gadget programs (Litinski lattice-surgery forms).

    Convention: data logical qubits live in block `0`, ancilla logical qubits
    in block `1`; classical outcomes `r₁ = 0, r₂ = 1, r₃ = 2`.  Each
    `if r = -1 then frame_P` desugars to `ite r skip (frame …)`, and
    conjunctions / inequalities to nested `ite`s. -/

/-- The data logical qubit `q = ⟨block 0, i⟩`. -/
abbrev dataQ (i : Nat) : LQubit := ⟨0, i⟩
/-- The ancilla logical qubit `a = ⟨block 1, i⟩`. -/
abbrev ancQ (i : Nat) : LQubit := ⟨1, i⟩

/-- **Hadamard gadget at arbitrary qubits** (data `q`, ancilla `anc` in `|0⟩`,
    fresh outcomes `r₁`, `r₂`):
    `r₁ := M_{ZX}(q,anc); r₂ := M_X(q);
     if r₁=-1 then frame_Z(anc); if r₂=-1 then frame_X(anc); discard q`. -/
def progHAt (q anc : LQubit) (r₁ r₂ : CVar) : Stmt :=
  .meas r₁ [(q, .Z), (anc, .X)] ;;
  .meas r₂ [(q, .X)] ;;
  .ite r₁ .skip (.frame anc .Z) ;;
  .ite r₂ .skip (.frame anc .X) ;;
  .discard q

/-- **Phase gadget at arbitrary qubits** (data `q`, ancilla `anc` in `|+⟩`). -/
def progSAt (q anc : LQubit) (r₁ r₂ : CVar) : Stmt :=
  .meas r₁ [(q, .Z), (anc, .Z)] ;;
  .meas r₂ [(q, .Y)] ;;
  .ite r₁ (.ite r₂ (.frame anc .Z) .skip) .skip ;;
  .ite r₁ .skip (.ite r₂ (.frame anc .Y) .skip) ;;
  .ite r₁ .skip (.ite r₂ .skip (.frame anc .X)) ;;
  .discard q

/-- **CNOT gadget at arbitrary qubits** (control `c`, target `t`, ancilla `anc`
    in `|+⟩`, fresh outcomes `r₁`, `r₂`, `r₃`). -/
def progCNOTAt (c t anc : LQubit) (r₁ r₂ r₃ : CVar) : Stmt :=
  .meas r₁ [(c, .Z), (anc, .Z)] ;;
  .meas r₂ [(anc, .X), (t, .X)] ;;
  .meas r₃ [(anc, .Z)] ;;
  .ite r₂ .skip (.frame c .Z) ;;
  .ite r₁ (.ite r₃ .skip (.frame t .X))
          (.ite r₃ (.frame t .X) .skip) ;;
  .discard anc

/-- **Controlled-Z gadget at arbitrary qubits** (DEMO placeholder, M16).  CZ is
    symmetric in `c`/`t`; this measurement-based gadget consumes the ancilla `anc`
    and leaves `c`,`t` live (it does NOT teleport the data, unlike `progHAt`).  The
    EXACT measurement pattern + channel correctness are the IDEAL-GADGET ASSUMPTION
    (deferred, like every PPM gadget here); it is shaped to TYPE-CHECK as a legal
    PPM fragment so a `czGate` source op has an implementation to lower to. -/
def progCZAt (c t anc : LQubit) (r₁ r₂ r₃ : CVar) : Stmt :=
  .meas r₁ [(c, .Z), (anc, .Z)] ;;
  .meas r₂ [(t, .Z), (anc, .Z)] ;;
  .meas r₃ [(anc, .X)] ;;
  .ite r₁ .skip (.frame t .Z) ;;
  .ite r₂ .skip (.frame c .Z) ;;
  .discard anc

/-- **Hadamard gadget** (ancilla `a = ⟨1,0⟩` in `|0⟩`) — the fixed-qubit
    instance of `progHAt` (data `⟨0,0⟩`, ancilla `⟨1,0⟩`, outcomes `0,1`). -/
def progH : Stmt := progHAt (dataQ 0) (ancQ 0) 0 1

/-- **Phase gadget** — the fixed-qubit instance of `progSAt`. -/
def progS : Stmt := progSAt (dataQ 0) (ancQ 0) 0 1

/-- **CNOT gadget** (control `c = ⟨0,0⟩`, target `t = ⟨0,1⟩`, ancilla `a = ⟨1,0⟩`)
    — the fixed-qubit instance of `progCNOTAt`. -/
def progCNOT : Stmt := progCNOTAt (dataQ 0) (dataQ 1) (ancQ 0) 0 1 2

/-- A post-selection **verification check** (cultivation): measure `P`, and
    `abort` unless the outcome is `+1`. -/
def checkPlus (r : CVar) (P : MTarget) : Stmt :=
  .meas r P ;; .ite r .skip .abort

-- The example programs use only well-formed (1- or 2-qubit) measurements.
example : MTarget.wf [(dataQ 0, .Z), (ancQ 0, .X)] = true := by decide
example : MTarget.wf [(dataQ 0, .X)] = true := by decide
example : MTarget.wf [(dataQ 0, .Z), (dataQ 0, .X)] = false := by decide  -- repeated qubit rejected

end PPM
