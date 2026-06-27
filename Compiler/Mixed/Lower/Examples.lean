/-
  Compiler.Mixed.Lower.Examples — the §5 / M12 / M13 / M14 executable tests for the
  resource-aware compiler (and the `k=2` fixture `tenvQ2`), split out of
  Compiler/Mixed/Lower.lean.
-/
import Compiler.Mixed.Lower.Public
import Compiler.Mixed.Lower.ProgramOk

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical

/-- A valid two-LOGICAL-qubit block (k = 2). -/
def tenvQ2 : TypedEnv :=
  ⟨[⟨{ n := 2, stab := [], lx := [[true, false, false, false], [false, true, false, false]],
       lz := [[false, false, true, false], [false, false, false, true]] }, by decide⟩]⟩

/-! ## §5. Executable tests (separate from the theorems above). -/

-- source typing: H on the live bare qubit is well-formed; on a discarded qubit it is not:
example : srcOpOk tenvQ PPMState.init (.hGate ⟨0, 0⟩) = true := by decide
example : srcOpOk tenvQ ⟨[], [⟨0, 0⟩]⟩ (.hGate ⟨0, 0⟩) = false := by decide
-- resource-aware compile lowers H to a DIRECT transversal:
example : (match compileOpR [] tenvQ PPMState.init ⟨1, 0⟩ 0 1 2 (.hGate ⟨0, 0⟩) with
           | .ok (.transversal _ _, _, _) => true | _ => false) = true := by decide
-- compileProgram threads env + resources + fresh vars over a small program:
example : ok? (compileProgram [] ⟨1, 0⟩ tenvQ PPMState.init 0
    [.measure 0 [(⟨0, 0⟩, PPM.PLetter.Z)], .hGate ⟨0, 0⟩]) = true := by decide
-- …and the compiled program type-checks (this is `compileProgram_sound` instantiated):
example : (match compileProgram [] ⟨1, 0⟩ tenvQ PPMState.init 0 [.hGate ⟨0, 0⟩] with
           | .ok (prog, _, _) => ok? (checkLogicalExec [] tenvQ prog) | _ => false) = true := by decide

/-! ### §5·M12. Contract tests (bug fixes + evidence-carrying interface). -/

-- (M15 task 1/2) UNIFIED `compile?` with a mandatory SOURCE TYPECHECK.
-- The operand bug is FIXED: BOTH modes reject a bad logical index BEFORE lowering.
example : ok? (compile? .executable  { caps := [], anc := ⟨0, 0⟩ } tenvQ [.hGate ⟨0, 99⟩]) = false := by decide
example : ok? (compile? .moduloMagic { caps := [], anc := ⟨0, 0⟩ } tenvQ [.hGate ⟨0, 99⟩]) = false := by decide
example : ok? (compile? .executable  { caps := [], anc := ⟨0, 0⟩ } tenvQ [.sGate ⟨0, 99⟩]) = false := by decide
-- a CNOT with control = target is rejected by the source typecheck:
example : ok? (compile? .executable { caps := [], anc := ⟨0, 0⟩ } tenvQ [.cnotGate ⟨0, 0⟩ ⟨0, 0⟩]) = false := by decide
-- magic policy is the MODE: `executable` rejects `T`, `moduloMagic` accepts it (typed obligation).
example : ok? (compile? .executable  { caps := [], anc := ⟨0, 0⟩ } tenvQ [.tGate ⟨0, 0⟩]) = false := by decide
example : ok? (compile? .moduloMagic { caps := [], anc := ⟨0, 0⟩ } tenvQ [.tGate ⟨0, 0⟩]) = true := by decide
-- both modes reject an INVALID `T` operand (source typecheck fires before the magic policy):
example : ok? (compile? .moduloMagic { caps := [], anc := ⟨0, 0⟩ } tenvQ [.tGate ⟨0, 99⟩]) = false := by decide
-- a valid H/S program compiles in executable mode:
example : ok? (compile? .executable { caps := [], anc := ⟨0, 0⟩ } tenvQ [.hGate ⟨0, 0⟩, .sGate ⟨0, 0⟩]) = true := by decide
-- A magic-containing program type-checks (modulo magic) but is NOT executable-shaped:
example : ok? (checkLogicalExec [] tenvQ [.magic { kind := .tGate, target := ⟨0, 0⟩ }]) = true := by decide
example : progNoMagic [MixedInstr.magic { kind := .tGate, target := ⟨0, 0⟩ }] = false := by decide
example : progNoMagic [MixedInstr.transversal 0 hGate2x2] = true := by decide
-- ProgramOk T/magic policy unchanged (admits T only under allowMagic):
example : ProgramOk [] ⟨⟨0, 0⟩, true⟩  tenvQ PPMState.init 0 [.tGate ⟨0, 0⟩] = true  := by decide
example : ProgramOk [] ⟨⟨0, 0⟩, false⟩ tenvQ PPMState.init 0 [.tGate ⟨0, 0⟩] = false := by decide

-- compileProgramLoc / compile? emit a program ACCEPTED by the checker.
example : (match compileProgramLoc [] ⟨1, 0⟩ tenvQ PPMState.init 0 []
              [.measure 0 [(⟨0, 0⟩, PPM.PLetter.Z)], .hGate ⟨0, 0⟩] with
           | .ok (prog, _, _, _) => ok? (checkLogicalExec [] tenvQ prog) | _ => false) = true := by decide
example : (match compile? .executable { caps := [], anc := ⟨1, 0⟩ } tenvQ [.hGate ⟨0, 0⟩, .sGate ⟨0, 0⟩] with
           | .ok c => ok? (checkLogicalExec [] tenvQ c.prog) | _ => false) = true := by decide

-- A discarded logical qubit cannot be reused — by a direct gate, PPM, or switch:
example : ok? (checkLogicalExec [] tenvQ [.ppm (.discard ⟨0, 0⟩), .transversal 0 hGate2x2]) = false := by decide
example : ok? (checkLogicalExec [] tenvQ [.ppm (.discard ⟨0, 0⟩), .ppm (.frame ⟨0, 0⟩ .X)]) = false := by decide

/-! ### §5·M13. Ancilla allocation discipline (fixes M12 `single-anc-reuse`). -/

-- Successive allocations are FRESH and DISTINCT (no single-ancilla reuse).
example : (AncillaSupply.fromQ ⟨1, 0⟩).alloc.1 = ⟨1, 0⟩ := by decide
example : ((AncillaSupply.fromQ ⟨1, 0⟩).alloc.2).alloc.1 = ⟨1, 1⟩ := by decide
example : (AncillaSupply.fromQ ⟨1, 0⟩).alloc.1 ≠ ((AncillaSupply.fromQ ⟨1, 0⟩).alloc.2).alloc.1 := by decide
-- Two H fallbacks on the SAME canonical qubit, given DISTINCT allocated ancillas,
-- relocate it to the NEWEST ancilla — and the two ancillas are distinct (vs M12,
-- where both fallbacks reused one fixed ancilla).
example :
    let a0 := (AncillaSupply.fromQ ⟨1, 0⟩).alloc.1
    let a1 := ((AncillaSupply.fromQ ⟨1, 0⟩).alloc.2).alloc.1
    let m1 := relocateOnFallback a0 (.hGate ⟨0, 0⟩) (.ppm (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)])) []
    let m2 := relocateOnFallback a1 (.hGate ⟨0, 0⟩) (.ppm (.meas 1 [(⟨0, 0⟩, PPM.PLetter.Z)])) m1
    a0 ≠ a1 ∧ LocMap.loc m2 ⟨0, 0⟩ = a1 := by decide
-- The allocating compiler threads the supply: a 2-op program advances `next` by 2.
example : (match compileProgramLocA [] tenvQ PPMState.init 0 [] (AncillaSupply.fromQ ⟨1, 0⟩)
              [.hGate ⟨0, 0⟩, .hGate ⟨0, 0⟩] with
           | .ok (_, _, _, _, sup) => sup.next == 2 | _ => false) = true := by decide
-- …and the allocating public path still type-checks its emitted program.
example : (match compile? .executable { caps := [], anc := ⟨1, 0⟩ } tenvQ [.hGate ⟨0, 0⟩, .sGate ⟨0, 0⟩] with
           | .ok c => ok? (checkLogicalExec [] tenvQ c.prog) | _ => false) = true := by decide

/-! ### §5·M13. Block-level direct transversal (honest direct-gate syntax). -/

-- A DIRECT transversal is a BLOCK-LEVEL op: `blockTransversal b g` emits a
-- `.transversal b g` (acting on the WHOLE block `b`), the honest direct-gate form.
example : (match compileOpR [] tenvQ PPMState.init ⟨1, 0⟩ 0 1 2 (.blockTransversal 0 hGate2x2) with
           | .ok (.transversal b g, _, _) => b == 0 && g == hGate2x2 | _ => false) = true := by decide
example : srcOpOk tenvQ PPMState.init (.blockTransversal 0 hGate2x2) = true := by decide
example : ProgramOk [] ⟨⟨0, 0⟩, false⟩ tenvQ PPMState.init 0 [.blockTransversal 0 hGate2x2] = true := by decide
-- On a SINGLE-LOGICAL block (k=1, `tenvQ`) the per-qubit `hGate ⟨0,0⟩` and the
-- block-level `blockTransversal 0 H` have the SAME (block-wide) symplectic action —
-- so the `hGate` shorthand is HONEST exactly here (one logical qubit per block).
example : LogicalOp.srcAction tenvQ (.hGate ⟨0, 0⟩)
        = LogicalOp.srcAction tenvQ (.blockTransversal 0 hGate2x2) := by decide

/-! ### §5·M14. Addressability: `hGate`/`sGate` direct ONLY on a single-logical block.

    `tenvQ2` is a VALID `k=2` block (two logical qubits, `n=2`, no stabilizers). -/

-- `singleLogicalBlock` distinguishes k=1 from k>1:
example : singleLogicalBlock tenvQ 0 = true := by decide
example : singleLogicalBlock tenvQ2 0 = false := by decide
-- k=1: `hGate ⟨0,0⟩` MAY compile to a direct (block = qubit) transversal:
example : (match compileOpR [] tenvQ PPMState.init ⟨1, 0⟩ 0 1 2 (.hGate ⟨0, 0⟩) with
           | .ok (.transversal _ _, _, _) => true | _ => false) = true := by decide
-- k>1: `hGate ⟨0,1⟩` must NOT compile to a block-wide `.transversal` (it needs a
-- qubit-level gadget, which fails here ⇒ explicit error — NEVER a block-wide H):
example : (match compileOpR [] tenvQ2 PPMState.init ⟨1, 0⟩ 0 1 2 (.hGate ⟨0, 1⟩) with
           | .ok (.transversal _ _, _, _) => true | _ => false) = false := by decide
-- but `blockTransversal 0 H` STILL compiles block-wide on the SAME k>1 block:
example : (match compileOpR [] tenvQ2 PPMState.init ⟨1, 0⟩ 0 1 2 (.blockTransversal 0 hGate2x2) with
           | .ok (.transversal b _, _, _) => b == 0 | _ => false) = true := by decide
-- and the source ACTION no longer pretends `hGate ⟨0,1⟩` is a block-wide H on a k>1 block:
example : LogicalOp.srcAction tenvQ2 (.hGate ⟨0, 1⟩) = none := by decide
example : LogicalOp.srcAction tenvQ2 (.blockTransversal 0 hGate2x2) ≠ none := by decide

/-! ### §5·M14. Checked ancilla pool (proof-carrying allocation). -/

-- Allocation from an EMPTY pool fails:
example : ok? (AncillaPool.alloc tenvQ PPMState.init .zero ⟨[]⟩) = false := by decide
-- Allocation of an INVALID (out-of-range) ancilla fails:
example : ok? (AncillaPool.alloc tenvQ PPMState.init .zero ⟨[⟨⟨5, 0⟩, .zero, .available⟩]⟩) = false := by decide
-- Allocation of a DISCARDED-qubit ancilla fails:
example : ok? (AncillaPool.alloc tenvQ ⟨[], [⟨0, 0⟩]⟩ .zero ⟨[⟨⟨0, 0⟩, .zero, .available⟩]⟩) = false := by decide
-- WRONG-basis allocation fails (pool holds |+⟩, request |0⟩):
example : ok? (AncillaPool.alloc tenvQ PPMState.init .zero ⟨[⟨⟨0, 0⟩, .plus, .available⟩]⟩) = false := by decide
-- A CONSUMED ancilla is never re-issued (single-entry pool ⇒ second alloc fails):
example : (match AncillaPool.alloc tenvQ PPMState.init .zero ⟨[⟨⟨0, 0⟩, .zero, .available⟩]⟩ with
           | .ok (_, p) => ok? (AncillaPool.alloc tenvQ PPMState.init .zero p) | _ => false) = false := by decide
-- Two allocations from a 2-entry pool consume DISTINCT ancillas:
example : (match AncillaPool.alloc tenvQ2 PPMState.init .zero
              ⟨[⟨⟨0, 0⟩, .zero, .available⟩, ⟨⟨0, 1⟩, .zero, .available⟩]⟩ with
           | .ok (q1, p) => (match AncillaPool.alloc tenvQ2 PPMState.init .zero p with
                             | .ok (q2, _) => ! (q1 == q2) | _ => false)
           | _ => false) = true := by decide
-- A valid allocation IS valid + live (the `alloc_valid` soundness lemma, witnessed):
example : (match AncillaPool.alloc tenvQ PPMState.init .zero ⟨[⟨⟨0, 0⟩, .zero, .available⟩]⟩ with
           | .ok (q, _) => validLQubit tenvQ q && ! PPMState.init.dead.contains q | _ => false) = true := by decide

end Compiler
