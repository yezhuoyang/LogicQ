<p align="center">
  <img src="assets/logicq-logo.svg" alt="LogicQ — verified QEC compilation in Lean 4" width="560">
</p>

<p align="center">
  <b>A &ldquo;quantum CompCert&rdquo;: a Lean&nbsp;4 verified compiler from chain-complex&ndash;typed fault-tolerant programs down to a physical Clifford&nbsp;+&nbsp;measurement target.</b>
</p>

<p align="center">
  <img alt="Lean" src="https://img.shields.io/badge/Lean-v4.29.1-blue">
  <img alt="Mathlib" src="https://img.shields.io/badge/Mathlib-v4.29.1-blue">
  <img alt="core" src="https://img.shields.io/badge/core-mostly%20Mathlib--free-success">
  <img alt="proofs" src="https://img.shields.io/badge/soundness-propext--clean-success">
  <img alt="license" src="https://img.shields.io/badge/license-MIT-green">
</p>

---

LogicQ is a Lean&nbsp;4 workspace for a verified quantum-error-correction (QEC) compilation stack.
The code is organized as a tower of **small languages**, each with its own syntax,
semantics, and checker, connected by lowering passes whose soundness theorems are
kernel-checked.

<p align="center">
  <img src="assets/quantum-hardware.svg" alt="A dilution refrigerator, control lines, and an error-corrected qubit chip" width="720">
</p>

Quantum error correction protects a handful of *logical* qubits by spreading them across
many noisy *physical* qubits on a chip cooled inside a dilution refrigerator (above).
Turning a high-level fault-tolerant program into the exact sequence of physical Clifford
gates and stabilizer measurements such a machine must run is a long, error-prone
compilation. LogicQ makes **every stage of that translation a typed, checked artifact** —
and, for the wired passes, *proves* that lowering preserves the intended logical action.

## The stack

<p align="center">
  <img src="assets/pipeline.svg" alt="LogicQ compilation pipeline: ChainQ to TypeChecker to Mixed IR to QStab to QClifford, with planned surgery and PPR/PPM passes" width="940">
</p>

The currently **wired** compiler path is:

```text
ChainQ code families  →  TypeChecker.TypedEnv  →  Compiler LogicalOp  →  Mixed IR
```

plus the physical extraction edges `Mixed / PPM  →  QStab  →  QClifford`.

The longer **target** stack — some stages exist today as standalone verified language
specs, with the passes between them planned — is:

```text
ChainQ  →  PPR  →  PPM  →  surgery / adapter  →  QStab  →  QClifford
```

Each box above is a small language with its own syntax, semantics, and checker.
Solid arrows are wired edges with soundness theorems; dashed arrows are planned passes
or standalone specs.

> **Honest scope.** LogicQ is careful to separate what is *proved* from what is *assumed*
> or *planned*. Soundness theorems are `propext`-clean (**not** advertised as
> &ldquo;axiom-free&rdquo;). Static legality, addressing, and resource discipline are proved;
> physical **channel correctness, code distance, decoders, and fault tolerance are explicit
> deferred obligations** — never silently assumed. The full tier-by-tier contract is in
> **[Compiler/CONTRACT.md](Compiler/CONTRACT.md)**; the design rationale is in
> **[DESIGN.md](DESIGN.md)**.

## Layers at a glance

| Folder | Layer | What lives there |
|---|---|---|
| [Logical](Logical/README.md) | vocabulary | logical block ids and the `LQubit` address scheme shared by every IR |
| [Physical](Physical/README.md) | vocabulary | physical qubit addresses and the dense 4-letter Pauli alphabet |
| [ChainQ](ChainQ/README.md) | `L_FE` front-end | CSS / stabilizer code families, type-checked into proof-carrying `CheckedCSSCode` |
| [TypeChecker](TypeChecker/README.md) | legality | accepts a logical op only when a finite GF(2)/symplectic certificate recomputes |
| [Compiler](Compiler/README.md) | lowering | `Source LogicalOp → Mixed IR` (`compile?`) + bridges toward QStab/QClifford |
| [PPR](PPR/README.md) | `L_PPR` spec | logical Pauli-product rotations `exp(i φ P)` with a Mathlib denotation |
| [PPM](PPM/README.md) | `L_PPM` spec | adaptive Pauli-product measurement programs (QMeas) |
| [MagicQ](MagicQ/README.md) | magic states | cultivation + Bravyi–Kitaev 15-to-1 distillation protocol checker |
| [QStab](QStab/README.md) | `L_QStab` target | physical stabilizer-measurement classical dataflow |
| [QClifford](QClifford/README.md) | `L_QClifford` target | physical Clifford gates + measurement circuits |
| [CodeSwitching](CodeSwitching/README.md) | reserved | source-level switching stub (real legality in TypeChecker/Judgment/Switch + Compiler/CodeSwitch) |
| [LatticeSurgery](LatticeSurgery/README.md) | reserved | surgery-language stub (real surgery IR lives in [Compiler/LS](Compiler/LS/README.md)) |
| [Library](Library/README.md) | references | vendored arXiv sources and notes (source-only; gitignored) |

**Inside the compiler** ([Compiler/README.md](Compiler/README.md)): the
[Mixed IR](Compiler/Mixed/README.md) target and [its lowering](Compiler/Mixed/Lower/README.md);
the verified [ChainQ2Mixed](Compiler/ChainQ2Mixed/README.md) front-end (path + schedule +
QGPU/qLDPC); the [QStab2QClifford](Compiler/QStab2QClifford/README.md) syndrome-extraction
pass; the [OpenQASM-2 front-end](Compiler/QASM/README.md); the
[lattice-surgery IR](Compiler/LS/README.md); the
[code-switch certificates](Compiler/CodeSwitch/README.md); the
[state-vector Simulator](Compiler/Simulator/README.md); and the worked
[Demo](Compiler/Demo/README.md) programs.

## Concrete examples for each layer

Every snippet below is **real code from the repository**, closed `by decide` or stated as a
proved theorem. Each one links to its source.

### 1 · Logical & Physical — the shared vocabulary

Every IR addresses qubits the same way: the `idx`-th logical qubit of a logical block, and a
dense Pauli alphabet for the physical target.

```lean
-- Logical/Basic.lean
structure LQubit where
  blk : BlockId
  idx : Nat
  deriving DecidableEq, Repr, Inhabited
```

```lean
-- Physical/Basic.lean — the dense 4-letter Pauli string of the physical target
example : ofString "ZZI" = [.Z, .Z, .I] := by decide
```

→ [Logical/](Logical/README.md) · [Physical/](Physical/README.md)

### 2 · ChainQ — declare & type-check a QEC code family

A user declares a code family; ChainQ elaborates and *type-checks* it (shape, CSS commutation
`H_X·H_Zᵀ = 0`, logical-class membership) into a validity-carrying `CheckedCSSCode`.

```lean
example : isOk ((CodeDecl.surface 3).check?) = true := by decide
example : isOk ((CodeDecl.toric 2).check?) = true := by decide
example : isOk ((CodeDecl.bb 3 3 [(0, 0), (1, 0), (0, 2)] [(0, 0), (2, 0), (0, 1)]).check?) = true := by decide
example : isOk ((CodeDecl.liftedProduct 3 [[[0], [1]]] 1 2).check?) = true := by decide
```

→ [ChainQ/Syntax.lean](ChainQ/Syntax.lean) · [ChainQ/](ChainQ/README.md)

### 3 · TypeChecker — is this logical operation legal on this code?

The distinctive judgment is a **proof-carrying capability matcher**: a cross-code joint
measurement `Z̄ ⊗ Z̄` is rejected unless an installed lattice-surgery/code-switch capability
recomputes a valid merged-code certificate.

```lean
-- a single-block logical measurement is native:
example : ok? (checkPPM tenvQ [] [(⟨0, 0⟩, PPM.PLetter.Z)]) = true := by decide
-- a cross-code joint Z̄⊗Z̄ PPM with NO capability is rejected …
example : ok? (checkPPM tenvQR [] zzTarget) = false := by decide
-- … and ADMITTED only with a valid adapter capability:
example : ok? (checkPPM tenvQR [zzCap] zzTarget) = true := by decide
```

→ [TypeChecker/Judgment/PPM/Examples.lean](TypeChecker/Judgment/PPM/Examples.lean) · [TypeChecker/](TypeChecker/README.md)

### 4 · Compiler / Mixed IR — compile *and run*, end to end

`H; S` lowers to direct transversals and `execMixed`-runs to the **same state** as the ideal
source simulator — exact-operational equality (`GadgetBoundary.exact`), not an assumption.

```lean
def hsSrc : List LogicalOp := [.hGate ⟨0, 0⟩, .sGate ⟨0, 0⟩]

example : (match compile? .executable demoCfg tenvQ hsSrc with
           | .ok c => decide (execMixed (Layout.flat 4) 1 c.prog (init 1)
                              = some (runGates 1 (sourceGates (Layout.flat 4) hsSrc) (init 1)))
           | .error _ => false) = true := by decide
example : hsSrc.all (fun op => opBoundary op == GadgetBoundary.exact) = true := by decide
```

→ [Compiler/Demo/Contract.lean](Compiler/Demo/Contract.lean) · [Compiler/Mixed/](Compiler/Mixed/README.md)

### 5 · ChainQ2Mixed — request ≠ realization (verified transversal CNOT)

The front-end separates *what* a logical op requests from *how* it is realized. The verified
homomorphic-CNOT path **rejects a zero physical incidence** that claims to implement a logical
CNOT — the lifted symplectic map would induce the identity, not the CNOT.

```lean
example : ok? (checkPrim? [] cnotEnv PPMState.init (.transversalCNOT cnotSpec)) = true := by decide
-- a ZERO physical incidence that requests a logical CNOT is rejected:
example : ok? (checkPrim? [] cnotEnv PPMState.init
    (.transversalBatch { controlBlock := 0, targetBlock := 1, incidence := [[false]], logicalIncidence := [[true]] })) = false := by decide
```

→ [Compiler/ChainQ2Mixed/Primitive.lean](Compiler/ChainQ2Mixed/Primitive.lean) · [Compiler/ChainQ2Mixed/](Compiler/ChainQ2Mixed/README.md)

### 6 · PPR — logical Pauli-product rotations

The `L_PPR` spec: programs are sequences of `exp(i φ P)` rotations with a Mathlib denotation and
a proved composition law. T-count is a structural fold over the program.

```lean
def rotT (q : LQubit) : Rot := ⟨⟨false, .piEighth⟩, [(q, .Z)]⟩
def rotS (q : LQubit) : Rot := ⟨⟨false, .piQuarter⟩, [(q, .Z)]⟩
def rotZZ (q₁ q₂ : LQubit) : Rot := ⟨⟨false, .piEighth⟩, [(q₁, .Z), (q₂, .Z)]⟩

example : RotProg.tCount [rotT ⟨0, 0⟩, rotS ⟨0, 0⟩, rotZZ ⟨0, 0⟩ ⟨0, 1⟩] = 2 := by decide
example : RotProg.wf [rotT ⟨0, 0⟩, rotS ⟨0, 0⟩, rotZZ ⟨0, 0⟩ ⟨0, 1⟩] = true := by decide
```

→ [PPR/Syntax.lean](PPR/Syntax.lean) · [PPR/](PPR/README.md)

### 7 · PPM — adaptive Pauli-product measurement (QMeas)

The `L_PPM` measurement language; its alphabet is restricted to the natively
lattice-surgery-realizable one- and two-body logical observables.

```lean
example : MTarget.wf [(dataQ 0, .Z), (ancQ 0, .X)] = true := by decide
example : MTarget.wf [(dataQ 0, .X)] = true := by decide
example : MTarget.wf [(dataQ 0, .Z), (dataQ 0, .X)] = false := by decide  -- repeated qubit rejected
```

→ [PPM/Syntax.lean](PPM/Syntax.lean) · [PPM/](PPM/README.md)

### 8 · Code switching — a transparent cross-code coercion

Encoding a bare qubit into the `[[3,1,1]]` repetition code is a legal switch that **preserves
the logical operators** (induced `X̄ = XXX`); a degenerate all-zero map is rejected.

```lean
def encF : BoolMat := [[true, true, true, false, false, false],
                       [false, false, false, true, false, false]]

example : ok? (checkSwitch tsrc 0 tdst { kind := .gaugeFix, f := encF }) = true := by decide
example : (res? (checkSwitch tsrc 0 tdst { kind := .gaugeFix, f := encF })).map (·.2.inducedLX)
            = some [[true, true, true, false, false, false]] := by decide
example : ok? (checkSwitch tsrc 0 tdst { kind := .gaugeFix, f := zeroMat 2 6 }) = false := by decide
```

→ [TypeChecker/Judgment/Switch/Examples.lean](TypeChecker/Judgment/Switch/Examples.lean) · [Compiler/CodeSwitch/](Compiler/CodeSwitch/README.md)

### 9 · MagicQ — magic-state protocols

The checker accepts the standard 15-to-1 distillation (15 `T` inputs, one output), while the
non-Pauli Bravyi–Kitaev A-type syndrome stays an **explicit deferred obligation** rather than
being claimed proven.

```lean
example : checks? ReedMuller15.rm15To1 = true := by decide
-- the non-Pauli Bravyi–Kitaev A-type syndrome + decoding is recorded as DEFERRED:
example :
    ((checkProtocol ⟨[]⟩ ReedMuller15.rm15To1).toOption.map
      (fun cp => cp.deferred.contains .bkATypeSyndrome)) = some true := by decide
```

→ [MagicQ/Tests.lean](MagicQ/Tests.lean) · [MagicQ/](MagicQ/README.md)

### 10 · QStab — physical stabilizer-measurement dataflow

The `L_QStab` target is an SSA-style classical dataflow over physical Pauli measurements. A
single flipped check flips the **syndrome** but leaves the **logical output** untouched.

```lean
-- a flipped check c0 = -1 flips the syndrome d0 = c0 ⊕ c2 …
example : evalVar progReadout (fun k => decide (k = 0)) 3 = true := by decide
-- … but leaves the logical output o0 untouched:
example : evalVar progReadout (fun k => decide (k = 0)) 7 = false := by decide
```

→ [QStab/Semantics.lean](QStab/Semantics.lean) · [QStab/](QStab/README.md)

### 11 · QClifford — the physical Clifford + measurement target

The terminal `L_QClifford` IR: physical Clifford gates, Z-basis measurements, and
classically-conditioned Pauli corrections, with resource counters.

```lean
/-- A `CNOT(c,t)` realized from a `CZ`: `H t; CZ c t; H t`. -/
def cnotFromCZ (c t : PQubit) : Circuit := [.H t, .CZ c t, .H t]

example : (cnotFromCZ 0 1).gateCount = 3 := by decide
example : (cnotFromCZ 0 1).twoQubitCount = 1 := by decide
```

→ [QClifford/Syntax.lean](QClifford/Syntax.lean) · [QClifford/](QClifford/README.md)

### 12 · QStab → QClifford — the syndrome-extraction pass

A real lowering pass: each physical stabilizer `Prop` is extracted by a chosen scheme
(standard / destructive / Shor / Knill / flag). The standard-Z gadget compiles to a fresh
ancilla, two CNOTs from the data, and one measurement.

```lean
example : compileProp (stdZ 3 [1, 0]) 7 0 =
    [.prepZero 3, .CNOT 1 3, .CNOT 0 3, .meas 3 7] := by decide
```

→ [Compiler/QStab2QClifford/Basic.lean](Compiler/QStab2QClifford/Basic.lean) · [Compiler/QStab2QClifford/](Compiler/QStab2QClifford/README.md)

## Public imports

The repository root intentionally has no `.lean` files. Import public layers through their
folder-owned entrypoints:

```lean
import LogicQ.Basic        -- umbrella over the whole workspace
import ChainQ.Basic        -- front-end code type system
import TypeChecker.Basic   -- legality checker + soundness
import Compiler.Basic      -- Source LogicalOp → Mixed IR (the wired compiler)
import PPR.Basic           -- Pauli-product rotations (spec)
import PPM.Basic           -- adaptive Pauli-product measurement (spec)
import MagicQ.Basic        -- magic-state protocol checker
import QStab.Basic         -- physical stabilizer dataflow (spec)
import QClifford.Basic     -- physical Clifford target (spec)
```

Each source folder has its own README with the local syntax, semantic rule, and small examples.

## Build

```powershell
lake build
lake build LogicQ.Basic ChainQ.Basic TypeChecker.Basic Compiler.Basic
```

The project uses **Lean v4.29.1** and **Mathlib v4.29.1**. Most of the stack is Mathlib-free
(the front-end type system, PPM, QStab, and QClifford are pure `Bool`/`List`/`Nat`); Mathlib
enters only for the analytic PPR denotation (the complex-matrix meaning of `exp(i φ P)`).

## License

[MIT](LICENSE) © 2026 John ye.
