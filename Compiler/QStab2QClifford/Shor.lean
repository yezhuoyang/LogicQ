/-
  Compiler.QStab2QClifford.Shor — cat-state syndrome extraction with a verifier,
  transplanted from LeanQEC `QStab/QClifford/Shor.lean` (`shorCircuit`/`zShorCircuit`).

  Layout: data `order`, `|+⟩` (X) or `|0⟩` (Z) cat block `cats` (|cats| = |order|),
  one verifier `ver`.  The X-stabilizer value is the XOR-parity of the `n` cat
  measurements; the verifier is a SEPARATE cat-state-prep flag (NOT part of the
  syndrome — see `ExtractionSpec.syndromeOffsets`, which skips slot 0).

  Faithful structure (cat cascade, verifier coupling to the two cat ENDPOINTS,
  data coupling, X-basis `H`s) is kept in the no-op `plumbing`; the `measZ`s are
  grouped by the pass (identical for the classical trace — the only thing proved;
  informally real-host-equivalent on disjoint qubits, NOT proved here).  Fault
  tolerance / the verifier weight bound are NOT proven here (that is LeanQEC's
  Heisenberg layer, a different semantics).
-/
import Compiler.QStab2QClifford.Scheme

namespace Compiler.QStab2QClifford
open Physical

/-- Linear cat cascade `cat₀ → cat₁ → … → cat_{n-1}`. -/
def catCascade (cats : List PQubit) : Circuit :=
  (cats.zip (cats.drop 1)).map (fun p => QClifford.Gate.CNOT p.1 p.2)

/-- Shor X-check plumbing (everything except the `measZ`s): cat prep + cascade,
    verifier prep + endpoint couplings, data couplings (cat controls data), and the
    X-basis `H` on every cat qubit. -/
def shorXPlumbing (order cats : List PQubit) (ver : PQubit) : Circuit :=
  [QClifford.Gate.prepPlus (cats.headD 0)] ++ catCascade cats ++
    [QClifford.Gate.prepZero ver, QClifford.Gate.CNOT (cats.headD 0) ver,
     QClifford.Gate.CNOT (cats.getLastD 0) ver] ++
    (cats.zip order).map (fun p => QClifford.Gate.CNOT p.1 p.2) ++
    cats.map (fun c => QClifford.Gate.H c)

/-- Shor Z-check plumbing: cat prep (`|0⟩`) + cascade, `|+⟩` verifier controlling the
    two cat endpoints then `H` (X-basis read), data couplings (data controls cat).
    Cat qubits are read in the Z basis (no `H`). -/
def shorZPlumbing (order cats : List PQubit) (ver : PQubit) : Circuit :=
  [QClifford.Gate.prepZero (cats.headD 0)] ++ catCascade cats ++
    [QClifford.Gate.prepPlus ver, QClifford.Gate.CNOT ver (cats.headD 0),
     QClifford.Gate.CNOT ver (cats.getLastD 0), QClifford.Gate.H ver] ++
    (order.zip cats).map (fun p => QClifford.Gate.CNOT p.1 p.2)

theorem noMeasParity_shorXPlumbing (order cats : List PQubit) (ver : PQubit) :
    noMeasParity (shorXPlumbing order cats ver) = true := by
  simp [shorXPlumbing, catCascade, noMeasParity, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

theorem noMeasParity_shorZPlumbing (order cats : List PQubit) (ver : PQubit) :
    noMeasParity (shorZPlumbing order cats ver) = true := by
  simp [shorZPlumbing, catCascade, noMeasParity, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

end Compiler.QStab2QClifford
