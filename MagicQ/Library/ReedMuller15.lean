/-
  MagicQ.Library.ReedMuller15 — the Bravyi–Kitaev 15-qubit punctured Reed–Muller
  CSS code and the standard 15-to-1 (`rm15_to_1`) distillation protocol AST.

  Grounded in quant-ph/0403025 ("Universal Quantum Computation with ideal Clifford
  gates and noisy ancillas", Bravyi–Kitaev) §"15-qubit code":

    * A Boolean function `f` of four variables has table `[f] ∈ 𝔽₂¹⁵` = its values
      at the 15 NONZERO inputs `0001,0010,…,1111` (puncturing `f(0000)`).
    * 𝓛₁ = span([x₁],[x₂],[x₃],[x₄])  (the four LINEAR generators); it is the dual
      of the [15,11] Hamming code.
    * 𝓛₂ = 𝓛₁ ⊕ span of the six QUADRATIC generators `[xᵢxⱼ]`.
    * The code is `CSS(σ_z, 𝓛₂; A, 𝓛₁)`: 10 Z-type checks from 𝓛₂, 4 X/A-type
      checks from 𝓛₁.  By the paper's weight lemma `𝓛₁ ⊆ 𝓛₂^⊥`, so it is a valid
      CSS code with `k = 15 − rank 𝓛₁ − rank 𝓛₂ = 15 − 4 − 10 = 1`: the `[[15,1,3]]`
      code.

  This pass builds the CHECKED binary CSS SURROGATE (shape / CSS-condition /
  logical-arity validity, by `decide`) and the `rm15_to_1` protocol AST with the
  symbolic (deferred, not proven) quality facts.  IMPORTANT: the 𝓛₁ checks are the
  NON-Pauli `A = (X+Y)/√2` operators with an `A`-type syndrome `η` — the ordinary
  `CSSCode` below validates only the BINARY subspace structure, NOT the `A`-type
  checks / `η` decoding / distillation correctness (those are the deferred
  `bkATypeSyndrome` obligation).  The threshold/output-error/success-probability are
  carried as strings — NOT proofs.

  Mathlib-free.
-/
import MagicQ.Check

namespace MagicQ.ReedMuller15
open ChainQ ChainQ.GF2

/-! ## §1. The punctured Reed–Muller generators. -/

/-- The 15 punctured coordinates: the nonzero inputs `1..15` (the paper drops
    `f(0000)`).  Coordinate `k` is the input `(x₁x₂x₃x₄)` with `k = 8x₁+4x₂+2x₃+x₄`. -/
def coords : List Nat := (List.range 15).map (· + 1)

/-- The indicator bit of input variable `xⱼ` (`j ∈ {1,2,3,4}`, `x₁` most
    significant) at coordinate `k`. -/
def xbit (j k : Nat) : Bool := k.testBit (4 - j)

/-- The LINEAR generator `[xⱼ] ∈ 𝔽₂¹⁵` (weight 8). -/
def lin (j : Nat) : BoolVec := coords.map (xbit j)

/-- The QUADRATIC generator `[xᵢxⱼ] ∈ 𝔽₂¹⁵` (weight 4). -/
def quad (i j : Nat) : BoolVec := coords.map (fun k => xbit i k && xbit j k)

/-- The four linear generators spanning 𝓛₁. -/
def linGens : BoolMat := [lin 1, lin 2, lin 3, lin 4]

/-- The six quadratic generators `[xᵢxⱼ]`. -/
def quadGens : BoolMat := [quad 1 2, quad 1 3, quad 1 4, quad 2 3, quad 2 4, quad 3 4]

/-- 𝓛₁ — the 4 X/A-type checks. -/
def L1 : BoolMat := linGens

/-- 𝓛₂ = 𝓛₁ ⊕ quadratics — the 10 Z-type checks. -/
def L2 : BoolMat := linGens ++ quadGens

/-- The BINARY CSS SURROGATE for the Bravyi–Kitaev 15-qubit code: the GF(2)
    subspaces 𝓛₁ and 𝓛₂ packaged as an ordinary Pauli `CSSCode` (`hx := 𝓛₁`,
    `hz := 𝓛₂`).

    HONESTY (do NOT over-read this): the real BK code is `CSS(σ_z, 𝓛₂; A, 𝓛₁)` where
    the 𝓛₁ checks are the NON-Pauli `A = (X+Y)/√2` operators with an `A`-type syndrome
    `η` (quant-ph/0403025 §"15-qubit code"; success ⟺ `η = 0`).  This `CSSCode` reuses
    ChainQ's ordinary Pauli-CSS machinery to validate ONLY the BINARY SUBSPACE
    STRUCTURE / shape — `rm15Code.valid = true` proves `𝓛₁ ⊆ 𝓛₂^⊥` and `k = 1`, NOT
    the `A`-type checks, the `η` decoding, or any 15-to-1 distillation semantics.
    Those non-Pauli parts are recorded as the deferred `Obligation.bkATypeSyndrome`
    (emitted by `distill15To1`). -/
def rm15Code : CSSCode := { n := 15, hx := L1, hz := L2 }

/-! ## §2. Checked structural facts (shape / CSS / rank / dimension), by `decide`. -/

/-- The Hamming weight of a row. -/
def wt (v : BoolVec) : Nat := v.foldl (fun a b => if b then a + 1 else a) 0

-- generator shapes and counts:
example : L1.length = 4 := by decide
example : L2.length = 10 := by decide
example : (L1.map (·.length)).all (· == 15) = true := by decide
example : (L2.map (·.length)).all (· == 15) = true := by decide

-- the paper's weight lemma (linear gens weight 8, quadratic gens weight 4):
example : (linGens.map wt).all (· == 8) = true := by decide
example : (quadGens.map wt).all (· == 4) = true := by decide

-- ranks: dim 𝓛₁ = 4, dim 𝓛₂ = 10:
example : rank L1 = 4 := by decide
example : rank L2 = 10 := by decide

-- the BINARY CSS SURROGATE is well-typed (Hₓ·H_zᵀ = 0, i.e. 𝓛₁ ⊆ 𝓛₂^⊥) and encodes
-- ONE logical.  NB: this proves the reused binary subspace structure ONLY — NOT the
-- BK A-type (non-Pauli) checks, the η decoding, or 15-to-1 distillation correctness.
example : rm15Code.valid = true := by decide
example : rm15Code.k = 1 := by decide
example : rm15Code.n = 15 := by decide

/-! ## §3. Symbolic quality facts (deferred — NOT proven in this pass). -/

/-- The input error parameter `ε`. -/
def epsSym : String := "ε"
/-- Success probability `p_s = (1 + 15(1−2ε)⁸)/16`. -/
def successProbSym : String := "p_s = (1 + 15·(1 - 2ε)^8) / 16"
/-- Distillation threshold precondition. -/
def thresholdSym : String := "ε < 0.141"
/-- Leading output error `ε_out ≈ 35·ε³`. -/
def outErrorSym : String := "ε_out = 35·ε^3 + O(ε^4)"

/-- The claimed quality of a single distilled output `T` (`A₀ = T|+⟩`).  The
    `[[15,1,3]]` code distance is a STRUCTURAL fact (validated separately in §2 at the
    `CSSCode` level, though the distance bound itself is not proven), NOT a gated
    distance promise — so it is recorded as a deferred claim rather than as
    `codeDistance` (which the `output` gate would demand a prior op establish, and
    distillation establishes no protocol-op distance). -/
def rm15OutQuality : MagicQuality :=
  { rawError      := some epsSym
    outputError   := some outErrorSym
    successProb   := some successProbSym
    deferred      := [thresholdSym, outErrorSym, successProbSym,
                      "output on Bravyi–Kitaev [[15,1,3]] code (distance 3 structural; not proven here)"] }

/-- The claimed quality of one raw (noisy) input `T`. -/
def rawInputQuality : MagicQuality := { rawError := some epsSym }

/-! ## §4. The `rm15_to_1` protocol AST. -/

/-- Supply the `i`-th raw `T` input as an external resource on its own carrier
    (carrier id = resource id = `i`).

    FIXTURE/SCAFFOLD: the 15 distillation inputs are EXTERNALLY-supplied noisy `T`
    states, not in-protocol injections; we model each as `inject` with the
    `.supplied` style on an `external "noisy-T-input"` carrier, reusing the existing
    linear-resource machinery rather than adding a new op.  TODO: a first-class
    protocol-input surface (a dedicated `ProtocolOp.input` / protocol input
    signature) is the intended final source-language design; this representation is
    a scaffold, not that design. -/
def injectInput (i : Nat) : ProtocolOp :=
  .inject .supplied .T i (.external "noisy-T-input") i rawInputQuality

/-- The 15 supplied raw inputs (resources `0..14`). -/
def inputInjections : List ProtocolOp := (List.range 15).map injectInput

/-- **The standard 15-to-1 distillation protocol** (Bravyi–Kitaev).  Consumes 15
    noisy `T` inputs, measures the syndrome, postselects `η = 0`, decodes, and
    returns ONE improved `T` (resource `15`) on the `[[15,1,3]]` carrier.  The
    quality facts (success probability, threshold, cubic output error) are carried
    SYMBOLICALLY as deferred obligations. -/
def rm15To1 : Protocol :=
  { name   := "rm15_to_1"
    params := { injectStyle := .unitary
                notes := ["Bravyi–Kitaev 15-to-1, quant-ph/0403025",
                          "input convention |A₀⟩ = T|+⟩ up to Clifford"] }
    ops    := inputInjections ++
      [ .distill15To1 (List.range 15) 15 15 (.external "RM15-[[15,1,3]]")
          rm15OutQuality ["rm15.z-syndrome", "rm15.eta"]
      , .postselect (.syndromeEq "rm15.eta" false)   -- η = 0
      , .output 15 ]
    spec   := [successProbSym, thresholdSym, outErrorSym,
               "output on [[15,1,3]] code; distance 3 structural (deferred)"] }

/-- A `rm15_to_1` variant given FEWER than 15 inputs — must be REJECTED. -/
def rm15To1Underfull : Protocol :=
  { rm15To1 with
    name := "rm15_to_1_underfull"
    ops  := (inputInjections.take 14) ++
      [ .distill15To1 (List.range 14) 15 15 (.external "RM15-[[15,1,3]]")
          rm15OutQuality ["rm15.eta"]
      , .output 15 ] }

end MagicQ.ReedMuller15
