/-
  Compiler.QStab2QClifford.Scheme — the extraction-scheme spec, schedule
  well-formedness, and per-scheme measurement metadata.

  An `ExtractionSpec` says HOW one QStab `Prop` (one physical Pauli measurement)
  is realised as a concrete QClifford gadget.  Schemes transplanted from LeanQEC
  (`QStab/QClifford/{Standard,Shor,Knill,Flag,Flag2General}.lean`):

    * standardX/Z      — one shared ancilla (LeanQEC `Standard.xCircuit`/`zCircuit`)
    * destructiveX/Z   — terminal one-qubit readout (LogicQ-local convenience)
    * shorX/Z          — cat-state block + verifier (LeanQEC `Shor.shorCircuit`)
    * knillX/Z         — transversal: one fresh ancilla per data qubit (LeanQEC `Knill`)
    * flagX            — single Chao–Reichardt flag (LeanQEC `FlagGeneral`)
    * flag2X           — two interleaved flags (LeanQEC `Flag2General`, scope ≤ weight 4)

  A scheme either binds its syndrome bit DIRECTLY (one measurement → the result
  var) or emits SEVERAL physical measurements into fresh auxiliary bits and a
  final classical `parity` of the SYNDROME subset (`syndromeOffsets`, transplanted
  from LeanQEC `readoutOffsets`).  Verifier/flag bits are recorded but are NOT part
  of the syndrome parity.

  This file is pure data (no proofs about `run`).
-/
import QStab.Basic
import Compiler.QStab2QClifford.Trace

namespace Compiler.QStab2QClifford

open Physical

/-- How one QStab `Prop` is lowered.  Helper qubits (ancilla / cat block /
    verifier / flags) are carried explicitly (LogicQ uses `PQubit := Nat`, so there
    are no `Fin`/`≠` proofs — distinctness is a Boolean schedule check). -/
inductive ExtractionSpec
  /-- Standard X-check: one `|+⟩` ancilla controls the data CNOTs. -/
  | standardX (order : List PQubit) (anc : PQubit)
  /-- Standard Z-check: one `|0⟩` ancilla, data controls the CNOTs. -/
  | standardZ (order : List PQubit) (anc : PQubit)
  /-- Destructive one-qubit X readout (`H; measZ`). -/
  | destructiveX (q : PQubit)
  /-- Destructive one-qubit Z readout (`measZ`). -/
  | destructiveZ (q : PQubit)
  /-- Shor X-check: `|+⟩` cat block (`cats`) + verifier (`ver`). -/
  | shorX (order : List PQubit) (cats : List PQubit) (ver : PQubit)
  /-- Shor Z-check: `|0⟩` cat block + `|+⟩` verifier. -/
  | shorZ (order : List PQubit) (cats : List PQubit) (ver : PQubit)
  /-- Knill X-check: one fresh ancilla per data qubit, H-conjugated. -/
  | knillX (order : List PQubit) (ancs : List PQubit)
  /-- Knill Z-check: transversal CNOT, one fresh ancilla per data qubit. -/
  | knillZ (order : List PQubit) (ancs : List PQubit)
  /-- Single-flag X-check (Chao–Reichardt). -/
  | flagX (order : List PQubit) (anc : PQubit) (flag : PQubit)
  /-- Two-flag X-check (scope: weight ≤ 4). -/
  | flag2X (order : List PQubit) (anc : PQubit) (flag1 : PQubit) (flag2 : PQubit)
  deriving Repr, Inhabited

/-- The ordered data support a spec schedules. -/
def ExtractionSpec.order : ExtractionSpec → List PQubit
  | .standardX o _ | .standardZ o _ | .shorX o _ _ | .shorZ o _ _
  | .knillX o _ | .knillZ o _ | .flagX o _ _ | .flag2X o _ _ _ => o
  | .destructiveX q | .destructiveZ q => [q]

/-- Whether the scheme binds its syndrome by a SINGLE measurement straight into
    the result var (no auxiliary bits, no parity gate). -/
def ExtractionSpec.isDirect : ExtractionSpec → Bool
  | .standardX .. | .standardZ .. | .destructiveX .. | .destructiveZ .. => true
  | _ => false

/-- The physical qubits this gadget measures, IN ORDER (so the `i`-th
    measurement reads trace slot `k+i` into aux bit `a+i`).  For multi-measurement
    schemes the verifier/flag come first (offset 0), matching `syndromeOffsets`. -/
def ExtractionSpec.measuredList : ExtractionSpec → List PQubit
  | .standardX _ anc | .standardZ _ anc => [anc]
  | .destructiveX q | .destructiveZ q => [q]
  | .shorX _ cats ver | .shorZ _ cats ver => ver :: cats   -- verifier (offset 0) then cats
  | .knillX _ ancs | .knillZ _ ancs => ancs
  | .flagX _ anc flag => [anc, flag]                        -- syndrome (offset 0) then flag
  | .flag2X _ anc flag1 flag2 => [anc, flag1, flag2]

/-- Number of physical measurements the gadget performs (= trace slots consumed
    = auxiliary bits allocated for multi-measurement schemes). -/
def ExtractionSpec.measCount (spec : ExtractionSpec) : Nat := spec.measuredList.length

/-- Which measurement offsets (within this gadget's `measCount` slots) contribute
    to the SYNDROME parity.  Transplanted from LeanQEC `readoutOffsets`:
    Shor skips slot 0 (the verifier); Knill XORs all; Flag/Flag2 use only slot 0
    (the flag measurements are separate). -/
def ExtractionSpec.syndromeOffsets : ExtractionSpec → List Nat
  | .standardX .. | .standardZ .. | .destructiveX .. | .destructiveZ .. => [0]
  | .shorX _ cats _ | .shorZ _ cats _ => (List.range cats.length).map (· + 1)
  | .knillX _ ancs | .knillZ _ ancs => List.range ancs.length
  | .flagX .. | .flag2X .. => [0]

/-- The auxiliary store bits (offset from base `a`) XORed into the syndrome. -/
def ExtractionSpec.syndromeBits (spec : ExtractionSpec) (a : CBit) : List CBit :=
  spec.syndromeOffsets.map (fun j => a + j)

/-! ## Schedule well-formedness. -/

/-- Physical support of a dense Pauli string. -/
def supportOf (P : QStab.PauliString) : List PQubit :=
  (List.range P.length).filter (fun q => decide (¬ P.getD q Pauli.I = Pauli.I))

def nodupNat : List Nat → Bool
  | []      => true
  | x :: xs => ! xs.contains x && nodupNat xs

def sameMembers (a b : List Nat) : Bool :=
  a.all (fun x => b.contains x) && b.all (fun x => a.contains x)

def allOnSupportEq (P : QStab.PauliString) (order : List PQubit) (p : Pauli) : Bool :=
  order.all (fun q => decide (P.getD q Pauli.I = p))

/-- `order` is a duplicate-free permutation of the actual (non-empty) support of
    `P`, and every support qubit carries the SAME single-letter Pauli `p`. -/
def orderedSupportOk (P : QStab.PauliString) (order : List PQubit) (p : Pauli) : Bool :=
  let supp := supportOf P
  nodupNat order && sameMembers order supp && decide (0 < supp.length) &&
    allOnSupportEq P order p

/-- Helper qubits (ancilla / cat block / verifier / flags) are duplicate-free and
    live OUTSIDE the data register `[0, n)`, where `n = P.length` is the dense Pauli
    string length.  Requiring `n ≤ h` for every helper `h` rules out aliasing ANY
    data qubit — including data qubits that carry `I` in `P` and so are absent from
    the measured `order` (the previous "disjoint from `order`" check missed those). -/
def helpersOk (n : Nat) (helpers : List PQubit) : Bool :=
  nodupNat helpers && helpers.all (fun h => decide (n ≤ h))

/-- Per-scheme schedule checker for one physical Pauli measurement. -/
def extractionSpecOk (P : QStab.PauliString) (spec : ExtractionSpec) : Bool :=
  match spec with
  | .standardX order anc =>
      orderedSupportOk P order Pauli.X && helpersOk P.length [anc]
  | .standardZ order anc =>
      orderedSupportOk P order Pauli.Z && helpersOk P.length [anc]
  | .destructiveX q =>
      orderedSupportOk P [q] Pauli.X && decide (([q] : List PQubit).length = 1)
  | .destructiveZ q =>
      orderedSupportOk P [q] Pauli.Z && decide (([q] : List PQubit).length = 1)
  | .shorX order cats ver =>
      orderedSupportOk P order Pauli.X && decide (cats.length = order.length) &&
        helpersOk P.length (cats ++ [ver])
  | .shorZ order cats ver =>
      orderedSupportOk P order Pauli.Z && decide (cats.length = order.length) &&
        helpersOk P.length (cats ++ [ver])
  | .knillX order ancs =>
      orderedSupportOk P order Pauli.X && decide (ancs.length = order.length) &&
        helpersOk P.length ancs
  | .knillZ order ancs =>
      orderedSupportOk P order Pauli.Z && decide (ancs.length = order.length) &&
        helpersOk P.length ancs
  | .flagX order anc flag =>
      orderedSupportOk P order Pauli.X && helpersOk P.length [anc, flag]
  | .flag2X order anc flag1 flag2 =>
      orderedSupportOk P order Pauli.X && helpersOk P.length [anc, flag1, flag2] &&
        decide (order.length ≤ 4)   -- proven scope of the two-flag scheme

end Compiler.QStab2QClifford
