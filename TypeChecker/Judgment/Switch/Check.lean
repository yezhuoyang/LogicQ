/-
  TypeChecker.Judgment.Switch.Check — the code-switch checker `checkSwitch`,
  its raw entry point, and the checked-certificate builder.
-/
import TypeChecker.Judgment.Switch.Cert
import TypeChecker.Core.Block
import TypeChecker.Core.Error

namespace TypeChecker
open ChainQ ChainQ.GF2

/-- Apply a cross-code symplectic map `f` (`2n_C × 2n_D`) to Pauli rows
    (`v ↦ v · f`), reusing `GF2.matMul`. -/
def applyCross (dcols : Nat) (f rows : BoolMat) : BoolMat := matMul rows f dcols

/-- Whether `A` and `B` agree row-by-row modulo the row span of `S` (equal as
    logical operators).  Row counts must match (so `zip` cannot silently drop a
    row) and each paired row must have equal width (so `vecXor` cannot truncate). -/
def rowsEqualModSpan (S A B : BoolMat) : Bool :=
  decide (A.length = B.length) &&
  (A.zip B).all (fun p => decide (p.1.length = p.2.length) && inSpan S (vecXor p.1 p.2))

/-- The deferred fault-tolerance obligations per protocol (faithful to the papers). -/
def switchObligations : SwitchKind → List String
  | .gaugeFix        => ["code distance d_D", "single-shot / small-set-flip decoder threshold"]
  | .transversalCNOT => ["transversal CNOT availability", "fault distance R ≥ d", "postselection acceptance (d=2)"]
  | .dimensionJump   => ["Künneth merged-code distance", "product/LP chain structure", "frame byproduct"]
  | .teleport        => ["Bell-pair fidelity", "byproduct frame correction"]

/-- **MILESTONE 2.**  Check that block `b` (in code C) of a TYPED environment can
    be switched to the typed target code `D` by the coercion `cert`, consuming and
    transforming the source.  Both source and target are pre-validated by their
    types (`TypedEnv`/`TypedBlock`), so there is NO `Block.valid` recheck and NO
    "target failure reported as source id" bug.  Returns the post-switch typed
    environment and the switch evidence. -/
def checkSwitch (Γ : TypedEnv) (b : BlockId) (D : TypedBlock) (cert : SwitchCert) :
    Except TypeError (TypedEnv × TypedSwitch) :=
  match Γ.block? b with
  | none => .error (.badBlock b)
  | some tb =>
    let C := tb.block
    let Dblk := D.block
    if !C.live then
      .error .notLive
    else if !(decide (C.own = Owned.owned)) then
      .error .notOwned                                   -- a borrowed block cannot be switched
    else if !(decide (cert.f.length = 2 * C.n) && cert.f.all (fun r => decide (r.length = 2 * Dblk.n))) then
      .error (.shapeMismatch "switch certificate f must be 2·n_C × 2·n_D")
    else if !(decide (C.lx.length = Dblk.lx.length) && decide (C.lz.length = Dblk.lz.length)) then
      .error (.shapeMismatch "logical arity mismatch (k_C ≠ k_D for X or Z logicals)")
    else
      let dc := 2 * Dblk.n
      let fS  := applyCross dc cert.f C.stab
      let fLX := applyCross dc cert.f C.lx
      let fLZ := applyCross dc cert.f C.lz
      if !(fS.all (fun r => inSpan Dblk.stab r)) then
        .error .stabilizerNotPreserved
      else if !(rowsEqualModSpan Dblk.stab fLX Dblk.lx) then
        .error (.certFailed "switch must preserve logical X̄ (f(X̄_C) ≠ X̄_D mod S_D)")
      else if !(rowsEqualModSpan Dblk.stab fLZ Dblk.lz) then
        .error (.certFailed "switch must preserve logical Z̄ (f(Z̄_C) ≠ Z̄_D mod S_D)")
      else
        -- the post-switch block is `D` made live and inheriting C's ownership; its
        -- validity is `D`'s (Block.valid ignores live/own), so it stays a TypedBlock.
        let newTB : TypedBlock := ⟨{ Dblk with live := true, own := C.own }, D.valid⟩
        .ok (⟨Γ.blocks.set b newTB⟩,
             { block := b, kind := cert.kind, toN := Dblk.n,
               inducedLX := fLX, inducedLZ := fLZ,
               obligations := switchObligations cert.kind })

/-- Validate a raw target code into a `TypedBlock`, reporting a TARGET-code error
    (`malformedTarget`) — never a source block id. -/
def toTargetBlock? (D : Block) : Except TypeError TypedBlock :=
  if h : Block.valid D = true then .ok ⟨D, h⟩ else .error .malformedTarget

/-- Raw entry point: validate the environment and target once, then switch. -/
def checkSwitchFromEnv (Γ : Env) (b : BlockId) (D : Block) (cert : SwitchCert) :
    Except TypeError (TypedEnv × TypedSwitch) := do
  let tΓ ← TypedEnv.ofEnv? Γ
  let tD ← toTargetBlock? D
  checkSwitch tΓ b tD cert

/-- A switch certificate whose map `f` is PROVEN to be `2·nC × 2·nD` (indexed by
    the source/target sizes).  Constructed only via `mkSwitchCert?`. -/
structure CheckedSwitchCert (nC nD : Nat) where
  cert    : SwitchCert
  shapeWf : (decide (cert.f.length = 2 * nC) && cert.f.all (fun r => decide (r.length = 2 * nD))) = true

/-- Validate that `cert.f` is exactly `2·nC × 2·nD`. -/
def mkSwitchCert? (cert : SwitchCert) (nC nD : Nat) : Except TypeError (CheckedSwitchCert nC nD) :=
  if h : (decide (cert.f.length = 2 * nC) && cert.f.all (fun r => decide (r.length = 2 * nD))) = true then
    .ok ⟨cert, h⟩
  else .error (.shapeMismatch "switch certificate f must be 2·n_C × 2·n_D")

end TypeChecker
