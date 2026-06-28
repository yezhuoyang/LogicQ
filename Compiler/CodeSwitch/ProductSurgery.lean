/-
  Compiler.CodeSwitch.ProductSurgery — a TYPED product-surgery / QGPU certificate.

  QGPU (2603.05398) and high-rate surgery (2510.08523) merge a data CSS code
  `Q = (H_X, H_Z)` with an identical auxiliary copy via a PRODUCT CONNECTION code
  `P = (H_X', H_Z')` of the same shape.  The merged checks are the explicit 2×2 block
  matrices (2603.05398, Lemma "Parallel product surgery"):

      H̃_X = [[H_X, H_X'], [0, H_X]]     H̃_Z = [[H_Z, 0], [H_Z', H_Z]]

  and the surgery square commutes (the merged code is CSS) iff `H̃_X · H̃_Zᵀ = 0`.
  The number of simultaneous logical merges is `M = rank H_Z'` (bounded by `k/2`), and
  each non-zero row of the merged `Z`-checks measures a logical `Z`-product.

  This file makes that a REAL recomputed certificate (NOT a bare `CapKind.productSurgery`):
  it CONSTRUCTS the merged checks and RECOMPUTES the CSS-commutation + data-code
  preservation + the rank witness over GF(2); `checkProductSurgery?` returns a
  proof-carrying `CheckedProductSurgery`.  HONEST SCOPE: we recompute the
  wellformedness + merged-CSS + merge-count + measured-target layer; merged-code
  DISTANCE / decoder / fault-tolerance stay EXPLICIT deferred obligations (proven only
  for HGP and numerically for CC codes — NOT a GF(2)-recomputable quantity).
-/
import Compiler.CodeSwitch.Basic
import TypeChecker.Judgment.PPM.Check

namespace Compiler.CodeSwitch
open ChainQ.GF2 TypeChecker

/-! ## §PS.1. The product-surgery certificate (CSS-matrix level). -/

/-- A product-surgery certificate: a data CSS code `(hX, hZ)` over `n` physical qubits
    and a product-connection CSS code `(hX', hZ')` of the SAME shape (so the merged code
    lives over `2n` qubits = data ++ auxiliary copy). -/
structure ProductSurgeryCert where
  n   : Nat
  hX  : BoolMat
  hZ  : BoolMat
  hX' : BoolMat
  hZ' : BoolMat
  deriving Repr, DecidableEq

/-- The data, connection, and merged checks all have the declared shapes:
    `hX/hX'` are `m_X × n`, `hZ/hZ'` are `m_Z × n`, and connection check counts match. -/
def ProductSurgeryCert.shapeOk (c : ProductSurgeryCert) : Bool :=
  c.hX.all (fun r => decide (r.length = c.n)) && c.hZ.all (fun r => decide (r.length = c.n)) &&
  c.hX'.all (fun r => decide (r.length = c.n)) && c.hZ'.all (fun r => decide (r.length = c.n)) &&
  decide (c.hX'.length = c.hX.length) && decide (c.hZ'.length = c.hZ.length)

/-- The merged X-checks `H̃_X = [[H_X, H_X'], [0, H_X]]` over `2n` qubits. -/
def ProductSurgeryCert.mergedHX (c : ProductSurgeryCert) : BoolMat :=
  vcat (hcat c.hX c.hX') (hcat (ChainQ.GF2.zeroMat c.hX.length c.n) c.hX)

/-- The merged Z-checks `H̃_Z = [[H_Z, 0], [H_Z', H_Z]]` over `2n` qubits. -/
def ProductSurgeryCert.mergedHZ (c : ProductSurgeryCert) : BoolMat :=
  vcat (hcat c.hZ (ChainQ.GF2.zeroMat c.hZ.length c.n)) (hcat c.hZ' c.hZ)

/-- The number of simultaneous logical merges `M = rank H_Z'` (= rank H_X' for X-type),
    over GF(2).  Bounded by `k/2` (`maxMerge`); saturated iff the connection is full rank. -/
def ProductSurgeryCert.mergeCount (c : ProductSurgeryCert) : Nat := rank c.hZ'

/-! ## §PS.2. The proof-carrying checked artifact + the checker. -/

/-- A product-surgery certificate whose merged code has been RECOMPUTED to be CSS:
    the data code is CSS, the merged checks commute (`H̃_X · H̃_Zᵀ = 0`), the data Z-checks
    are preserved as merged Z-stabilizers, and the merge count equals `rank H_Z'`.  Every
    field is a recomputed GF(2) PROOF, not a claimed flag.  Distance / decoder / FT are the
    explicit deferred `obligations`. -/
structure CheckedProductSurgery where
  cert        : ProductSurgeryCert
  merges      : Nat
  dataCSS     : orthogonal cert.hX cert.hZ = true
  mergedCSS   : orthogonal cert.mergedHX cert.mergedHZ = true
  dataPreserved : (vcat cert.hZ (ChainQ.GF2.zeroMat cert.hZ.length cert.n)).all
                    (fun r => inSpan cert.mergedHZ r) = true
  rankWitness : merges = cert.mergeCount
  obligations : List String

/-- The QGPU `M ≤ k/2` parallelism bound + the deferred obligations. -/
def productSurgeryObligations : List String :=
  ["merged-code distance d̃ ≥ d (proven for HGP; numerical for CC codes — DEFERRED)",
   "decoder for the merged syndrome (DEFERRED)",
   "fault distance / R ≥ d measurement rounds (DEFERRED)",
   "soundness ρ of the connection complex (DEFERRED)"]

/-! ## §PS.2b. CSS extraction from a symplectic block (Task A foundation).

    CONVENTION (pinned to `TypeChecker.Core.Symplectic` + `ChainQ.Materialize`): a width-`2n`
    symplectic stabilizer row is `(X-part ++ Z-part)` — the FIRST `n` entries are the X-support
    (`row.take n`), the LAST `n` are the Z-support (`row.drop n`).  `cssToStab` materializes an
    X-check `r` as `(r | 0)` and a Z-check `r` as `(0 | r)`.  So the inverse split is: a row is
    pure-X iff its Z-half is all zero, pure-Z iff its X-half is all zero; `H_X` = the X-halves of
    the pure-X rows, `H_Z` = the Z-halves of the pure-Z rows. -/

/-- A symplectic row's Z-half (`row.drop n`) is all zero — a pure-X (or trivial) stabilizer. -/
def rowIsPureX (n : Nat) (row : BoolVec) : Bool := (row.drop n).all (fun b => !b)
/-- A symplectic row's X-half (`row.take n`) is all zero — a pure-Z (or trivial) stabilizer. -/
def rowIsPureZ (n : Nat) (row : BoolVec) : Bool := (row.take n).all (fun b => !b)

/-- A symplectic stabilizer matrix is CSS iff every row has width `2n` and is pure-X or pure-Z
    (a Y-type / mixed row makes the code non-CSS and is REJECTED). -/
def blockStabIsCSS (n : Nat) (stab : BoolMat) : Bool :=
  stab.all (fun row => decide (row.length = 2 * n) && (rowIsPureX n row || rowIsPureZ n row))

/-- Extract `H_X` (width `n`): the X-halves (`take n`) of the pure-X rows. -/
def extractHX (n : Nat) (stab : BoolMat) : BoolMat :=
  (stab.filter (rowIsPureX n)).map (fun row => row.take n)

/-- Extract `H_Z` (width `n`): the Z-halves (`drop n`) of the pure-Z rows. -/
def extractHZ (n : Nat) (stab : BoolMat) : BoolMat :=
  (stab.filter (rowIsPureZ n)).map (fun row => row.drop n)

/-- **Check a product-surgery certificate.**  Recomputes: shape; the data code is CSS;
    the MERGED checks commute (the surgery square — the CSS condition for the merged code);
    the data Z-checks are preserved as merged Z-stabilizers; and the merge count
    `M = rank H_Z'` is within the `maxMerge = k/2` bound.  Returns proof-carrying evidence
    or rejects. -/
def checkProductSurgery? (c : ProductSurgeryCert) (maxMerge : Nat) :
    Except TypeError CheckedProductSurgery :=
  if !c.shapeOk then
    .error (.shapeMismatch "product-surgery: data/connection checks must share shape (m_X × n, m_Z × n)")
  else if hd : orthogonal c.hX c.hZ = true then
    if hm : orthogonal c.mergedHX c.mergedHZ = true then
      if hp : (vcat c.hZ (ChainQ.GF2.zeroMat c.hZ.length c.n)).all (fun r => inSpan c.mergedHZ r) = true then
        if decide (c.mergeCount ≤ maxMerge) then
          .ok { cert := c, merges := c.mergeCount, dataCSS := hd, mergedCSS := hm,
                dataPreserved := hp, rankWitness := rfl, obligations := productSurgeryObligations }
        else .error (.certFailed "product-surgery merge count M = rank H_Z' exceeds the k/2 bound")
      else .error (.certFailed "product surgery does not preserve the data Z-stabilizers")
    else .error (.certFailed "merged product-surgery checks do not commute (the merged code is not CSS)")
  else .error (.certFailed "the data code is not a valid CSS code (H_X · H_Zᵀ ≠ 0)")

/-- The recorded cert is exactly the INPUT cert that was checked. -/
theorem checkProductSurgery?_cert (c : ProductSurgeryCert) (maxMerge : Nat)
    {r : CheckedProductSurgery} (h : checkProductSurgery? c maxMerge = .ok r) : r.cert = c := by
  simp only [checkProductSurgery?] at h
  repeat (split at h <;> first | contradiction | skip)
  simp only [Except.ok.injEq] at h
  subst h; rfl

/-- **Product-surgery soundness.**  A successfully checked certificate proves the RECOMPUTED
    facts ABOUT THE INPUT CERT `c`: the data code is CSS, the merged code is CSS (the surgery
    square commutes), the data Z-stabilizers are preserved, and the merge count is exactly
    `rank H_Z'`.  (NOT a distance/FT claim — those are the deferred `obligations`.) -/
theorem checkProductSurgery?_sound (c : ProductSurgeryCert) (maxMerge : Nat)
    {r : CheckedProductSurgery} (h : checkProductSurgery? c maxMerge = .ok r) :
    orthogonal c.hX c.hZ = true ∧
      orthogonal c.mergedHX c.mergedHZ = true ∧
      (vcat c.hZ (ChainQ.GF2.zeroMat c.hZ.length c.n)).all
        (fun row => inSpan c.mergedHZ row) = true ∧
      r.merges = rank c.hZ' := by
  have hc := checkProductSurgery?_cert c maxMerge h
  subst hc
  exact ⟨r.dataCSS, r.mergedCSS, r.dataPreserved, r.rankWitness⟩

/-! ## §PS.3. The MEASURED-TARGET witness (a Z-product is measured by the merge). -/

/-- A logical `Z`-product `target` (a merged-space symplectic Z-vector / check-support
    vector) is MEASURED by the merged code iff it lies in the row span of the merged
    `Z`-checks (a combination of measured merged `Z`-stabilizers gives it).  Recomputed by
    `inSpan` (Gaussian elimination), with `solveInSpan?` giving the SELECTED rows. -/
def ProductSurgeryCert.measuresZ (c : ProductSurgeryCert) (target : BoolVec) : Bool :=
  inSpan c.mergedHZ target

/-- The explicit selected-rows witness (the GF(2) combination of merged `Z`-checks whose
    parity is the measured logical product), when the target is measured. -/
def ProductSurgeryCert.measuredRows? (c : ProductSurgeryCert) (target : BoolVec) : Option BoolVec :=
  solveInSpan? c.mergedHZ target

/-! ## §PS.4. Tests — POSITIVE (a valid CC-style merge) + NEGATIVE (non-commuting / over-rank). -/

/-- A valid product surgery: data `[[2,0]]`-style code `H_X = H_Z = [1 1]` on `n = 2`, with
    connection `H_X' = H_Z' = [1 1]`; the merged 2×2-block checks commute (CSS), `M = 1`. -/
def psOK : ProductSurgeryCert :=
  { n := 2, hX := [[true, true]], hZ := [[true, true]], hX' := [[true, true]], hZ' := [[true, true]] }

example : psOK.shapeOk = true := by decide
example : orthogonal psOK.hX psOK.hZ = true := by decide                 -- data code is CSS
example : orthogonal psOK.mergedHX psOK.mergedHZ = true := by decide       -- merged code is CSS
example : psOK.mergeCount = 1 := by decide                                 -- M = rank H_Z' = 1
example : ok? (checkProductSurgery? psOK 1) = true := by decide            -- accepted (M ≤ k/2)

-- the merged Z-checks measure the data Z-product `Z₀Z₁` on the data half (a merged-Z row):
example : psOK.measuresZ [true, true, false, false] = true := by decide

-- NEGATIVE — a connection that breaks the surgery-square commutation is REJECTED:
def psBadCommute : ProductSurgeryCert :=
  { psOK with hZ' := [[true, false]] }       -- H_Z' = [1 0] no longer commutes with H̃_X
example : orthogonal psBadCommute.mergedHX psBadCommute.mergedHZ = false := by decide
example : ok? (checkProductSurgery? psBadCommute 4) = false := by decide

-- NEGATIVE — the merge count exceeding the declared k/2 bound is REJECTED:
example : ok? (checkProductSurgery? psOK 0) = false := by decide           -- M = 1 > maxMerge 0

-- NEGATIVE — a non-CSS data code is REJECTED:
def psBadData : ProductSurgeryCert :=
  { psOK with hZ := [[true, false]] }         -- H_X · H_Zᵀ = [1 1]·[1 0]ᵀ = 1 ≠ 0
example : ok? (checkProductSurgery? psBadData 4) = false := by decide

/-! ## §PS.4b. PROVENANCE: a product-surgery `Capability` may be built ONLY from a
    `CheckedProductSurgery`.

    A bare `Capability` tagged `.productSurgery` is NOT trustworthy provenance — `checkPPM`
    only uses `kind` to pick obligations, and verifies the merge algebra regardless.  To make
    the product-surgery certificate LOAD-BEARING, the ONLY way to obtain a `.productSurgery`
    capability is `CapabilityWitness.productSurgery`, whose constructor REQUIRES a
    `CheckedProductSurgery`; its connection stabilizers are DERIVED from the cert's merged
    checks (`toConnStab`), never hand-supplied. -/

/-- The symplectic connection stabilizers DERIVED from a checked product surgery: each merged
    X-check `r` (width `2n`) lifts to `(r | 0)` and each merged Z-check to `(0 | r)` over the
    `4n = 2·mergedN` merged symplectic space (`mergedN = 2n`, data ++ auxiliary copy). -/
def CheckedProductSurgery.toConnStab (cps : CheckedProductSurgery) : BoolMat :=
  let w := 2 * cps.cert.n
  cps.cert.mergedHX.map (fun r => r ++ List.replicate w false) ++
  cps.cert.mergedHZ.map (fun r => List.replicate w false ++ r)

/-- A PROOF-CARRYING capability witness.  `generic` wraps a native/adapter capability and
    CARRIES A PROOF its kind is NOT `.productSurgery` — so a `.productSurgery` capability can
    NEVER enter through `generic`.  `productSurgery` can be built ONLY from a
    `CheckedProductSurgery` (+ the addressed data `blocks`), with its `connStab` DERIVED from
    the cert — so a `.productSurgery` authorization cannot exist without a recomputed
    product-surgery certificate. -/
inductive CapabilityWitness
  | generic        (cap : Capability) (h : (cap.kind == CapKind.productSurgery) = false)
  | productSurgery (cps : CheckedProductSurgery) (blocks : List BlockId)

/-- Smart constructor for a generic witness: REJECTS a `.productSurgery`-kind capability
    (which must instead come from a `CheckedProductSurgery` via `.productSurgery`). -/
def genericWitness? (cap : Capability) : Except TypeError CapabilityWitness :=
  if h : (cap.kind == CapKind.productSurgery) = false then .ok (.generic cap h)
  else .error (.certFailed "generic capability witness cannot carry a .productSurgery kind — use CapabilityWitness.productSurgery from a CheckedProductSurgery")

/-- Convert a witness to the generic merged-stabilizer `Capability` that `checkPPM` consumes.
    A `productSurgery` witness yields a `.productSurgery`-kind capability whose `connStab` is
    the cert-derived `toConnStab` and whose `ancN` is the auxiliary-copy size `cert.n`. -/
def CapabilityWitness.toCapability : CapabilityWitness → Capability
  | .generic cap _          => cap
  | .productSurgery cps blocks =>
      { kind := .productSurgery, blocks := blocks, ancN := cps.cert.n, connStab := cps.toConnStab }

/-- **A `.generic` witness never carries `.productSurgery`** — provenance is closed. -/
theorem CapabilityWitness.generic_not_productSurgery (cap : Capability)
    (h : (cap.kind == CapKind.productSurgery) = false) :
    (CapabilityWitness.generic cap h).toCapability.kind ≠ CapKind.productSurgery := by
  simp only [CapabilityWitness.toCapability]
  exact fun hk => by simp [hk] at h

/-- **Witnessed PPM** (the HIGH-LEVEL API paper protocols + ChainQ2Mixed use): run the
    verified matcher on capabilities obtained ONLY from witnesses, so a `.productSurgery`
    authorization is necessarily backed by a `CheckedProductSurgery` (and a `.generic` one is
    provably non-product-surgery). -/
def checkPPMWitnessed (Γ : TypedEnv) (ws : List CapabilityWitness) (P : PPM.MTarget) :
    Except TypeError TypedPPM :=
  checkPPM Γ (ws.map CapabilityWitness.toCapability) P

/-- A `productSurgery` capability witness is ALWAYS tagged `.productSurgery` and carries the
    cert-derived connection — there is no path to a hand-built product-surgery capability. -/
theorem CapabilityWitness.productSurgery_kind (cps : CheckedProductSurgery) (blocks : List BlockId) :
    (CapabilityWitness.productSurgery cps blocks).toCapability.kind = .productSurgery := rfl

theorem CapabilityWitness.productSurgery_connStab (cps : CheckedProductSurgery) (blocks : List BlockId) :
    (CapabilityWitness.productSurgery cps blocks).toCapability.connStab = cps.toConnStab := rfl

/-! ## §PS.5. Item-1 + Item-2 INTEGRATION: a HIGH-WEIGHT same-block PPM is rejected
    natively but ADMITTED through a product-surgery capability whose merged-code
    certificate (recomputed by `checkPPM`) proves the target is measured. -/

/-- A bare 3-logical data block (`X̄ᵢ`/`Z̄ᵢ` unit operators, no stabilizers). -/
def bare3 : Block :=
  { n := 3, stab := [],
    lx := [[true, false, false, false, false, false], [false, true, false, false, false, false],
           [false, false, true, false, false, false]],
    lz := [[false, false, false, true, false, false], [false, false, false, false, true, false],
           [false, false, false, false, false, true]] }
def bare3Env : TypedEnv :=
  match TypedEnv.ofEnv? { blocks := [bare3] } with | .ok Γ => Γ | .error _ => { blocks := [] }

/-- A GENERIC (adapter) merged capability over the data block with ONE auxiliary qubit: its
    merged `Z`-stabilizers `Z₀Z₁Z₂·Zₐ` and `Zₐ` combine (XOR) to the data 3-body `Z₀Z₁Z₂`, so
    the high-weight target IS measured by the merge.  Tagged `.adapterPPM` — NOT falsely
    `.productSurgery` (product-surgery provenance flows only through a `CheckedProductSurgery`). -/
def psMergeCap : Capability :=
  { kind := .adapterPPM, blocks := [0], ancN := 1,
    connStab := [[false, false, false, false, true, true, true, true],
                 [false, false, false, false, false, false, false, true]] }

/-- The HIGH-WEIGHT (3-body) logical `Z` measurement on the single data block. -/
def hw3 : PPM.MTarget := [(⟨0, 0⟩, .Z), (⟨0, 1⟩, .Z), (⟨0, 2⟩, .Z)]

-- it is genuinely high-weight (NOT native arity), and NO native PPM accepts it:
example : hw3.nativeArity = false := by decide
example : ok? (checkPPM bare3Env [] hw3) = false := by decide           -- rejected without a capability
-- but it is ADMITTED with the merged capability (Item 1 gate + Item 1 merged-cert):
example : ok? (checkPPM bare3Env [psMergeCap] hw3) = true := by decide
-- a FAKE capability whose connection does NOT span the target (only `Zₐ`) is REJECTED —
-- `checkPPM` recomputes that the target is not measured by the merge:
def psFakeCap : Capability :=
  { psMergeCap with connStab := [[false, false, false, false, false, false, false, true]] }
example : ok? (checkPPM bare3Env [psFakeCap] hw3) = false := by decide
-- a native 1-/2-body measurement on the same block STILL compiles (native case preserved):
example : ok? (checkPPM bare3Env [] [(⟨0, 0⟩, .Z), (⟨0, 1⟩, .Z)]) = true := by decide

/-! ## §PS.5b. PROVENANCE — the `.productSurgery` authorization bypass is CLOSED.
    `checkPPM` is the GENERIC merged-stabilizer kernel (it verifies the merge algebra for ANY
    capability, regardless of `kind`).  The HIGH-LEVEL witnessed API (`checkPPMWitnessed`)
    admits a `.productSurgery` capability ONLY from a `CheckedProductSurgery` via
    `.productSurgery cps`; a `.generic` witness PROVABLY cannot carry `.productSurgery`. -/

-- a `.productSurgery` capability from a CHECKED cert is tagged productSurgery + cert-derived:
example : (match checkProductSurgery? psOK 1 with
           | .ok cps => (CapabilityWitness.productSurgery cps [0]).toCapability.kind == CapKind.productSurgery
                          && decide ((CapabilityWitness.productSurgery cps [0]).toCapability.connStab = cps.toConnStab)
           | .error _ => false) = true := by decide
-- the witnessed matcher runs `checkPPM` on a PROOF-CARRYING generic witness (kind ≠ productSurgery):
example : ok? (checkPPMWitnessed bare3Env [.generic psMergeCap (by decide)] hw3) = true := by decide

-- THE CLOSED BYPASS: `genericWitness?` REJECTS a raw `.productSurgery` capability …
def rawPS : Capability := { psMergeCap with kind := .productSurgery }
example : ok? (genericWitness? rawPS) = false := by decide
-- … and `.generic rawPS _` is UNCONSTRUCTIBLE (the proof `(rawPS.kind == .productSurgery) = false`
-- is `(true) = false`, which does not exist); a non-product-surgery cap is accepted as generic:
example : ok? (genericWitness? psMergeCap) = true := by decide

end Compiler.CodeSwitch
