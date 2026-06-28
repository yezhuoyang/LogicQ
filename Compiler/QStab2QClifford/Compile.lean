/-
  Compiler.QStab2QClifford.Compile — the public QStab → QClifford pass and its
  trace-host classical-dataflow correctness theorem.

  One QStab `Prop` lowers either to a DIRECT single measurement into its result
  var, or (Shor/Knill/Flag/Flag2) to several physical measurements into FRESH
  auxiliary bits plus a final classical `parity` of the syndrome subset.  The aux
  bits are allocated from a supply that STARTS ABOVE all SSA result vars
  (`a₀ = p.length`), so the one-Prop-binds-one-var convention is preserved.

  `compile?_trace_correct` (a faithful generalization of the M23 standard-only
  theorem) proves the emitted circuit, under the measurement-trace host, realises
  exactly the QStab SSA dataflow into a QClifford store — where each prop's result
  var is the XOR of its gadget's syndrome-measurement outcomes.  This is the
  classical-dataflow / compiler contract ONLY — NOT fault tolerance or a physical
  stabilizer-channel theorem.
-/
import Compiler.QStab2QClifford.Standard
import Compiler.QStab2QClifford.Shor
import Compiler.QStab2QClifford.Knill
import Compiler.QStab2QClifford.Flag

namespace Compiler.QStab2QClifford

open Physical

/-! ## The gadget circuit and its store effect. -/

/-- A multi-measurement gadget: plumbing, then a measurement of each `ms` qubit
    into fresh consecutive bits, then the syndrome parity into the result var. -/
def multiGadget (plumbing : Circuit) (ms : List PQubit) (synbits : List CBit) (v a : CBit) : Circuit :=
  plumbing ++ measGroup ms a ++ [QClifford.Gate.parity v synbits]

/-- The store a multi-measurement gadget leaves: aux bits hold the outcomes, the
    result var holds their syndrome XOR. -/
def multiStore (outcome : Nat → Bool) (ms : List PQubit) (synbits : List CBit)
    (v a k : Nat) (σ : Store) : Store :=
  (setOutcomes outcome ms a k σ).set v ((setOutcomes outcome ms a k σ).xorOf synbits)

/-- The no-op quantum plumbing of a multi-measurement scheme. -/
def schemePlumbing : ExtractionSpec → Circuit
  | .shorX order cats ver => shorXPlumbing order cats ver
  | .shorZ order cats ver => shorZPlumbing order cats ver
  | .knillX order ancs => knillXPlumbing order ancs
  | .knillZ order ancs => knillZPlumbing order ancs
  | .flagX order anc flag => flagXPlumbing order anc flag
  | .flag2X order anc flag1 flag2 => flag2XPlumbing order anc flag1 flag2
  | _ => []

theorem noMeasParity_schemePlumbing (spec : ExtractionSpec) :
    noMeasParity (schemePlumbing spec) = true := by
  cases spec with
  | shorX o c v => exact noMeasParity_shorXPlumbing o c v
  | shorZ o c v => exact noMeasParity_shorZPlumbing o c v
  | knillX o a => exact noMeasParity_knillXPlumbing o a
  | knillZ o a => exact noMeasParity_knillZPlumbing o a
  | flagX o a f => exact noMeasParity_flagXPlumbing o a f
  | flag2X o a f1 f2 => exact noMeasParity_flag2XPlumbing o a f1 f2
  | _ => rfl

theorem isDirect_measCount (spec : ExtractionSpec) (h : spec.isDirect = true) :
    spec.measCount = 1 := by
  cases spec <;> simp_all [ExtractionSpec.isDirect, ExtractionSpec.measCount, ExtractionSpec.measuredList]

/-- Lower one QStab `Prop` to its extraction gadget. -/
def compileProp (spec : ExtractionSpec) (v a : CBit) : Circuit :=
  if spec.isDirect then
    directPrefix spec ++ [QClifford.Gate.meas (directMeasQubit spec) v]
  else
    multiGadget (schemePlumbing spec) spec.measuredList (spec.syndromeBits a) v a

/-- The store one gadget leaves (extraction-local interpretation of its trace). -/
def propStoreUpdate (spec : ExtractionSpec) (v a : CBit) (outcome : Nat → Bool) (k : Nat) (σ : Store) :
    Store :=
  if spec.isDirect then
    σ.set v (outcome k)
  else
    multiStore outcome spec.measuredList (spec.syndromeBits a) v a k σ

/-- **Per-prop trace correctness**: the gadget consumes `measCount` slots and
    leaves `propStoreUpdate`. -/
theorem traceFold_compileProp (outcome : Nat → Bool) (spec : ExtractionSpec) (v a k : Nat) (σ : Store) :
    traceFold outcome (compileProp spec v a) k σ
      = (k + spec.measCount, propStoreUpdate spec v a outcome k σ) := by
  unfold compileProp propStoreUpdate
  split
  · next h =>
      rw [traceFold_directProp, isDirect_measCount spec h]
  · next h =>
      rw [multiGadget,
          traceFold_multiGadget outcome (schemePlumbing spec) spec.measuredList
            (spec.syndromeBits a) v a k σ (noMeasParity_schemePlumbing spec),
          ExtractionSpec.measCount, multiStore]

/-! ## Whole-program compilation. -/

/-- The compiler configuration supplies an extraction spec for the `i`-th `Prop`. -/
structure CompileConfig where
  specOf : Nat → ExtractionSpec

/-- The pass error alphabet. -/
inductive CompileError
  | sourceMalformed
  | badExtractionSchedule
  deriving Repr, DecidableEq

/-- Fresh auxiliary bits a gadget consumes (0 for the direct, single-meas schemes). -/
def auxCount (spec : ExtractionSpec) : Nat :=
  if spec.isDirect then 0 else spec.measCount

/-- Whole-program lowering: `v` = next SSA result var, `a` = next fresh aux bit,
    `i` = next `Prop` index (for `cfg.specOf`). -/
def compileFrom (cfg : CompileConfig) : QStab.Prog → (v a i : Nat) → Circuit
  | [], _, _, _ => []
  | .prop _ _ :: t, v, a, i =>
      let spec := cfg.specOf i
      compileProp spec v a ++ compileFrom cfg t (v + 1) (a + auxCount spec) (i + 1)
  | .parity srcs :: t, v, a, i =>
      QClifford.Gate.parity v srcs :: compileFrom cfg t (v + 1) a i

/-- Total physical measurements emitted from `Prop` index `i` onwards. -/
def totalMeas (cfg : CompileConfig) : QStab.Prog → Nat → Nat
  | [], _ => 0
  | .prop _ _ :: t, i => (cfg.specOf i).measCount + totalMeas cfg t (i + 1)
  | .parity _ :: t, i => totalMeas cfg t i

/-- The reference SSA dataflow into a QClifford store (extraction-local): a prop's
    result var gets its gadget's syndrome XOR; a parity var gets the XOR of its
    sources.  `v` = result var, `a` = aux base, `i` = prop index, `k` = trace cursor. -/
def applyQStabClassicalGen (cfg : CompileConfig) :
    QStab.Prog → (v a i k : Nat) → (Nat → Bool) → Store → Store
  | [], _, _, _, _, _, σ => σ
  | .prop _ _ :: t, v, a, i, k, outcome, σ =>
      let spec := cfg.specOf i
      applyQStabClassicalGen cfg t (v + 1) (a + auxCount spec) (i + 1) (k + spec.measCount) outcome
        (propStoreUpdate spec v a outcome k σ)
  | .parity srcs :: t, v, a, i, k, outcome, σ =>
      applyQStabClassicalGen cfg t (v + 1) a i k outcome (σ.set v (σ.xorOf srcs))

def specsOkFrom (cfg : CompileConfig) : QStab.Prog → Nat → Bool
  | [], _ => true
  | .prop _ P :: t, i => extractionSpecOk P (cfg.specOf i) && specsOkFrom cfg t (i + 1)
  | .parity _ :: t, i => specsOkFrom cfg t i

def specsOk (cfg : CompileConfig) (p : QStab.Prog) : Bool := specsOkFrom cfg p 0

/-- The compiled circuit (aux bits start above all SSA vars). -/
def compile (cfg : CompileConfig) (p : QStab.Prog) : Circuit :=
  compileFrom cfg p 0 p.length 0

/-- Checked QStab → QClifford compiler. -/
def compile? (cfg : CompileConfig) (p : QStab.Prog) : Except CompileError Circuit :=
  if p.wf then
    if specsOk cfg p then .ok (compile cfg p) else .error .badExtractionSchedule
  else .error .sourceMalformed

theorem compile?_wf {cfg : CompileConfig} {p : QStab.Prog} {c : Circuit}
    (h : compile? cfg p = .ok c) : p.wf = true := by
  unfold compile? at h; split at h
  · assumption
  · contradiction

theorem compile?_eq {cfg : CompileConfig} {p : QStab.Prog} {c : Circuit}
    (h : compile? cfg p = .ok c) : c = compile cfg p := by
  unfold compile? at h; split at h
  · split at h
    · simpa using h.symm
    · contradiction
  · contradiction

/-! ## Trace-host correctness (faithful store mirror). -/

theorem traceFold_compileFrom (cfg : CompileConfig) (p : QStab.Prog) (v a i k : Nat)
    (outcome : Nat → Bool) (σ : Store) :
    traceFold outcome (compileFrom cfg p v a i) k σ
      = (k + totalMeas cfg p i, applyQStabClassicalGen cfg p v a i k outcome σ) := by
  induction p generalizing v a i k σ with
  | nil => simp [compileFrom, totalMeas, applyQStabClassicalGen, traceFold]
  | cons s t ih =>
      cases s with
      | prop sched P =>
          simp only [compileFrom, totalMeas, applyQStabClassicalGen, traceFold_append,
            traceFold_compileProp, ih, Nat.add_assoc]
      | parity srcs =>
          simp only [compileFrom, totalMeas, applyQStabClassicalGen, traceFold, ih]

/-- Running the compiled program on the trace host realises the QStab SSA dataflow
    into the QClifford store (with auxiliary measurement bits as scratch). -/
theorem run_compileFrom_trace (cfg : CompileConfig) (p : QStab.Prog) (v a i k : Nat)
    (outcome : Nat → Bool) (σ : Store) :
    QClifford.run (traceHost outcome) (compileFrom cfg p v a i) { next := k } σ
      = ({ next := k + totalMeas cfg p i }, applyQStabClassicalGen cfg p v a i k outcome σ) := by
  rw [run_traceHost, traceFold_compileFrom]

/-- **Main contract (generalizes the M23 standard-only `compile?_trace_correct`)**:
    a successfully compiled program, run on the measurement-trace host, produces the
    QClifford store given by the extraction-local QStab SSA dataflow. -/
theorem compile?_trace_correct {cfg : CompileConfig} {p : QStab.Prog} {c : Circuit}
    (h : compile? cfg p = .ok c) (outcome : Nat → Bool) :
    QClifford.run (traceHost outcome) c { next := 0 } QClifford.Store.empty
      = ({ next := totalMeas cfg p 0 },
          applyQStabClassicalGen cfg p 0 p.length 0 0 outcome QClifford.Store.empty) := by
  rw [compile?_eq h, compile]
  simpa using run_compileFrom_trace cfg p 0 p.length 0 0 outcome QClifford.Store.empty

/-! ## Extraction-local syndrome: each prop's result var IS its physical syndrome.

    This makes the "agrees with the QStab SSA variables under an extraction-local
    interpretation of physical measurement traces" claim precise per gadget: the
    result var holds the syndrome — the single outcome (direct) or the XOR-parity of
    the gadget's SYNDROME measurements (multi); verifier/flag bits are excluded. -/

theorem setOutcomes_lt {α : Type} (outcome : Nat → Bool) (xs : List α) (b k i : Nat) (σ : Store)
    (hi : i < b) : setOutcomes outcome xs b k σ i = σ i := by
  induction xs generalizing b k σ with
  | nil => rfl
  | cons x xs ih =>
      rw [setOutcomes, ih (b + 1) (k + 1) (σ.set b (outcome k)) (by omega)]
      simp only [QClifford.Store.set]
      rw [if_neg (Nat.ne_of_lt hi)]

theorem setOutcomes_get {α : Type} (outcome : Nat → Bool) (xs : List α) (b k j : Nat) (σ : Store)
    (hj : j < xs.length) : setOutcomes outcome xs b k σ (b + j) = outcome (k + j) := by
  induction xs generalizing b k j σ with
  | nil => simp at hj
  | cons x xs ih =>
      rw [setOutcomes]
      cases j with
      | zero =>
          have h := setOutcomes_lt outcome xs (b + 1) (k + 1) b (σ.set b (outcome k))
            (Nat.lt_succ_self b)
          simp [Nat.add_zero, h, QClifford.Store.set]
      | succ j' =>
          show setOutcomes outcome xs (b + 1) (k + 1) (σ.set b (outcome k)) (b + (j' + 1))
              = outcome (k + (j' + 1))
          rw [show b + (j' + 1) = (b + 1) + j' from by omega,
            show k + (j' + 1) = (k + 1) + j' from by omega]
          exact ih (b + 1) (k + 1) j' (σ.set b (outcome k))
            (by simp only [List.length_cons] at hj; omega)

theorem foldl_xor_eq (f g : Nat → Bool) (l : List Nat) (h : ∀ j ∈ l, f j = g j) (acc : Bool) :
    l.foldl (fun b j => xor b (f j)) acc = l.foldl (fun b j => xor b (g j)) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, h x (by simp)]
      exact ih (fun j hj => h j (by simp [hj])) _

theorem syndromeOffsets_lt_measCount (spec : ExtractionSpec) :
    ∀ j ∈ spec.syndromeOffsets, j < spec.measCount := by
  cases spec <;> intro j hj <;>
    simp_all [ExtractionSpec.syndromeOffsets, ExtractionSpec.measCount, ExtractionSpec.measuredList,
      List.mem_map, List.mem_range] <;> omega

/-- The extraction-local syndrome of a gadget: the single measurement (direct) or
    the XOR of its SYNDROME physical measurements (multi). -/
def schemeSyndrome (spec : ExtractionSpec) (k : Nat) (outcome : Nat → Bool) : Bool :=
  if spec.isDirect then outcome k
  else spec.syndromeOffsets.foldl (fun b j => xor b (outcome (k + j))) false

/-- **Per-gadget agreement**: a prop's result var holds its extraction-local
    syndrome (the XOR of the physical syndrome-measurement outcomes). -/
theorem propStoreUpdate_resultVar (spec : ExtractionSpec) (v a k : Nat) (outcome : Nat → Bool)
    (σ : Store) :
    propStoreUpdate spec v a outcome k σ v = schemeSyndrome spec k outcome := by
  unfold propStoreUpdate schemeSyndrome
  split
  · simp [QClifford.Store.set]
  · rw [multiStore]
    simp only [QClifford.Store.set, QClifford.Store.xorOf,
      ExtractionSpec.syndromeBits, List.foldl_map]
    apply foldl_xor_eq
    intro j hj
    exact setOutcomes_get outcome spec.measuredList a k j σ (syndromeOffsets_lt_measCount spec j hj)

/-! ## Source-semantics bridge: the compiled store agrees with `QStab.evalVar`.

    `compile?_trace_correct` gives the compiled store as `applyQStabClassicalGen`.
    Here we connect THAT to the QStab source semantics (`QStab.eval`/`evalVar`):
    under the EXTRACTION-INDUCED prop-outcome stream (`extractedOutcome` — each
    prop's syndrome is the XOR of its physical measurements), every source variable
    `v < p.length` of the compiled store equals `QStab.evalVar p extractedOutcome v`.
    Classical dataflow ONLY — no physical-channel / fault-tolerance claim. -/

/-- The trace cursor at which the `j`-th `Prop` measures (sum of the earlier props'
    measurement counts). -/
def cursorOf (cfg : CompileConfig) : Nat → Nat
  | 0 => 0
  | j + 1 => cursorOf cfg j + (cfg.specOf j).measCount

/-- The prop-occurrence-indexed outcome stream the extraction pass induces: the
    `j`-th prop's syndrome, read from the physical trace at its cursor. -/
def extractedOutcome (cfg : CompileConfig) (outcome : Nat → Bool) (j : Nat) : Bool :=
  schemeSyndrome (cfg.specOf j) (cursorOf cfg j) outcome

/-- The reference SSA dataflow into a store using the EXTRACTED prop outcomes (no
    auxiliary bits) — the store mirror of `QStab.evalAux`. -/
def evalStore (cfg : CompileConfig) : QStab.Prog → (v i : Nat) → (Nat → Bool) → Store → Store
  | [], _, _, _, σ => σ
  | .prop _ _ :: t, v, i, outcome, σ =>
      evalStore cfg t (v + 1) (i + 1) outcome (σ.set v (extractedOutcome cfg outcome i))
  | .parity srcs :: t, v, i, outcome, σ =>
      evalStore cfg t (v + 1) i outcome (σ.set v (σ.xorOf srcs))

/-- A gadget only touches its result var `v` and auxiliary bits `≥ a`. -/
theorem propStoreUpdate_below (spec : ExtractionSpec) (v a k : Nat) (outcome : Nat → Bool)
    (σ : Store) (w : Nat) (hwv : w ≠ v) (hwa : w < a) :
    propStoreUpdate spec v a outcome k σ w = σ w := by
  unfold propStoreUpdate
  split
  · simp [QClifford.Store.set, hwv]
  · rw [multiStore]
    simp only [QClifford.Store.set, if_neg hwv]
    exact setOutcomes_lt outcome spec.measuredList a k w σ hwa

/-- Reading a store at the bit just written returns that value. -/
theorem store_set_self (σ : Store) (r : CBit) (b : Bool) :
    QClifford.Store.set σ r b r = b := by simp [QClifford.Store.set]

/-- `Store.xorOf` depends only on the values at its sources. -/
theorem xorOf_congr (σ₁ σ₂ : Store) (srcs : List CBit) (h : ∀ s ∈ srcs, σ₁ s = σ₂ s) :
    σ₁.xorOf srcs = σ₂.xorOf srcs := by
  simp only [QClifford.Store.xorOf]
  exact foldl_xor_eq (fun s => σ₁ s) (fun s => σ₂ s) srcs h false

/-- **Bridge step A**: the compiled store mirror agrees with `evalStore` on the
    result-var region, given the cursor matches the prop index and the aux base is
    above the region.  Aux bits (`≥ a`) and the SSA single-assignment discipline
    keep result vars from being clobbered. -/
theorem applyQStabClassicalGen_eq_evalStore (cfg : CompileConfig) (p : QStab.Prog) :
    ∀ (v a i k : Nat) (outcome : Nat → Bool) (σ₁ σ₂ : Store),
      QStab.Prog.wfFrom v p = true → v + p.length ≤ a → k = cursorOf cfg i →
      (∀ w, w < v → σ₁ w = σ₂ w) →
      ∀ w, w < v + p.length →
        applyQStabClassicalGen cfg p v a i k outcome σ₁ w = evalStore cfg p v i outcome σ₂ w := by
  induction p with
  | nil =>
      intro v a i k outcome σ₁ σ₂ _ _ _ hpre w hw
      simp only [List.length_nil, Nat.add_zero] at hw
      simpa only [applyQStabClassicalGen, evalStore] using hpre w hw
  | cons s t ih =>
      intro v a i k outcome σ₁ σ₂ hwf hav hk hpre w hw
      simp only [List.length_cons] at hav hw
      cases s with
      | prop sched P =>
          simp only [QStab.Prog.wfFrom] at hwf
          simp only [applyQStabClassicalGen, evalStore]
          refine ih (v + 1) (a + auxCount (cfg.specOf i)) (i + 1) (k + (cfg.specOf i).measCount)
            outcome _ _ hwf (by omega) ?_ ?_ w (by omega)
          · rw [hk]; rfl
          · intro w' hw'
            by_cases hwv : w' = v
            · subst hwv
              rw [propStoreUpdate_resultVar]
              simp [QClifford.Store.set, extractedOutcome, hk]
            · rw [propStoreUpdate_below _ _ _ _ _ _ _ hwv (by omega),
                QClifford.Store.set, if_neg hwv]
              exact hpre w' (by omega)
      | parity srcs =>
          simp only [QStab.Prog.wfFrom, Bool.and_eq_true] at hwf
          simp only [applyQStabClassicalGen, evalStore]
          refine ih (v + 1) a i k outcome _ _ hwf.2 (by omega) hk ?_ w (by omega)
          intro w' hw'
          by_cases hwv : w' = v
          · subst hwv
            rw [store_set_self, store_set_self]
            refine xorOf_congr _ _ srcs (fun s hs => hpre s ?_)
            simpa using (List.all_eq_true.mp hwf.1) s hs
          · simp only [QClifford.Store.set, if_neg hwv]
            exact hpre w' (by omega)

/-- `(l ++ [x])` read at index `l.length` is `x` (core `List.getD`, Mathlib-free). -/
theorem getD_concat_len {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.cons_append, List.length_cons, List.getD_cons_succ]; exact ih

/-- Reading `(l ++ l')` below `l.length` ignores `l'` (core `List.getD`, Mathlib-free). -/
theorem getD_append_lt {α : Type} (l l' : List α) (d : α) (w : Nat) (h : w < l.length) :
    (l ++ l').getD w d = l.getD w d := by
  induction l generalizing w with
  | nil => exact absurd h (by simp)
  | cons a l ih =>
      cases w with
      | zero => rfl
      | succ w =>
          rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]
          exact ih w (by simp only [List.length_cons] at h; omega)

/-- **Bridge step B (helper)**: `evalStore` equals the list-valued `QStab.evalAux`,
    pointwise on the result-var region. -/
theorem evalStore_eq_evalAux (cfg : CompileConfig) (p : QStab.Prog) :
    ∀ (v i : Nat) (outcome : Nat → Bool) (σ : Store) (acc : List Bool),
      QStab.Prog.wfFrom v p = true → acc.length = v →
      (∀ w, w < v → σ w = acc.getD w false) →
      ∀ w, w < v + p.length →
        evalStore cfg p v i outcome σ w
          = (QStab.evalAux p i (extractedOutcome cfg outcome) acc).getD w false := by
  induction p with
  | nil =>
      intro v i outcome σ acc _ _ hpre w hw
      simp only [List.length_nil, Nat.add_zero] at hw
      simpa only [evalStore, QStab.evalAux] using hpre w hw
  | cons s t ih =>
      intro v i outcome σ acc hwf hlen hpre w hw
      simp only [List.length_cons] at hw
      cases s with
      | prop sched P =>
          simp only [QStab.Prog.wfFrom] at hwf
          simp only [evalStore, QStab.evalAux]
          refine ih (v + 1) (i + 1) outcome _ _ hwf (by simp [hlen]) ?_ w (by omega)
          intro w' hw'
          by_cases hwv : w' = v
          · subst hwv
            rw [store_set_self, ← hlen, getD_concat_len]
          · rw [QClifford.Store.set, if_neg hwv, getD_append_lt acc _ _ w' (by omega)]
            exact hpre w' (by omega)
      | parity srcs =>
          simp only [QStab.Prog.wfFrom, Bool.and_eq_true] at hwf
          simp only [evalStore, QStab.evalAux]
          refine ih (v + 1) i outcome _ _ hwf.2 (by simp [hlen]) ?_ w (by omega)
          intro w' hw'
          by_cases hwv : w' = v
          · subst hwv
            rw [store_set_self, ← hlen, getD_concat_len, QClifford.Store.xorOf]
            refine foldl_xor_eq (fun s => σ s) (fun s => acc.getD s false) srcs (fun s hs => ?_) false
            exact hpre s (by simpa using (List.all_eq_true.mp hwf.1) s hs)
          · rw [QClifford.Store.set, if_neg hwv, getD_append_lt acc _ _ w' (by omega)]
            exact hpre w' (by omega)

/-- **Bridge step B**: at the top level, `evalStore` agrees with `QStab.evalVar`. -/
theorem evalStore_eq_evalVar (cfg : CompileConfig) (p : QStab.Prog) (outcome : Nat → Bool)
    (hwf : p.wf = true) (w : Nat) (hw : w < p.length) :
    evalStore cfg p 0 0 outcome QClifford.Store.empty w
      = QStab.evalVar p (extractedOutcome cfg outcome) w := by
  have := evalStore_eq_evalAux cfg p 0 0 outcome QClifford.Store.empty []
    hwf rfl (fun w hw => absurd hw (Nat.not_lt_zero w)) w (by simpa using hw)
  simpa [QStab.evalVar, QStab.eval] using this

/-- **Source-semantics bridge**: every source variable of the compiled store equals
    `QStab.evalVar` under the extraction-induced outcome stream. -/
theorem applyQStabClassicalGen_eq_evalVar (cfg : CompileConfig) (p : QStab.Prog)
    (outcome : Nat → Bool) (hwf : p.wf = true) (w : Nat) (hw : w < p.length) :
    applyQStabClassicalGen cfg p 0 p.length 0 0 outcome QClifford.Store.empty w
      = QStab.evalVar p (extractedOutcome cfg outcome) w := by
  rw [applyQStabClassicalGen_eq_evalStore cfg p 0 p.length 0 0 outcome
        QClifford.Store.empty QClifford.Store.empty hwf (by omega) rfl
        (fun w hw => rfl) w (by simpa using hw)]
  exact evalStore_eq_evalVar cfg p outcome hwf w hw

/-- **Run-level bridge**: a successfully compiled program, run on the trace host,
    agrees with `QStab.evalVar` on every source variable (under the extraction-induced
    outcome stream).  Classical-dataflow correctness only. -/
theorem compile?_trace_evalVar {cfg : CompileConfig} {p : QStab.Prog} {c : Circuit}
    (h : compile? cfg p = .ok c) (outcome : Nat → Bool) (w : Nat) (hw : w < p.length) :
    (QClifford.run (traceHost outcome) c { next := 0 } QClifford.Store.empty).2 w
      = QStab.evalVar p (extractedOutcome cfg outcome) w := by
  rw [compile?_trace_correct h outcome]
  exact applyQStabClassicalGen_eq_evalVar cfg p outcome (compile?_wf h) w hw

/-- Convenience predicates for examples. -/
def ok? : Except CompileError Circuit → Bool
  | .ok _ => true
  | .error _ => false

def err? (e : CompileError) : Except CompileError Circuit → Bool
  | .ok _ => false
  | .error e' => e' = e

end Compiler.QStab2QClifford
