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

## End-to-end LOC by layer

Here **LOC** means executable IR line count: one QASM instruction, one generated
ChainQ/LogicQ primitive, one MixedIR step, one QStab stabilizer instruction, or one final
QClifford gate. Declarations, comments, and barriers are excluded. The table splits QStab
into the resident-code syndrome pass and the logical-operation fragment, then shows their
total. The numbers below are checked in
[Compiler/QASM/Benchmarks.lean](Compiler/QASM/Benchmarks.lean) by `#guard` tests, using
the currently wired structural physical path.

The main scaling signal comes from nontrivial code blocks. Bare `d=1` rows are only smoke
tests: they map one logical qubit to one physical qubit, so equal counts across layers are
expected and do **not** demonstrate physical expansion.

| Example | Setup | QASM | LogicQ | MixedIR | Syn QStab | Logical QStab | Total QStab | QClifford | Width |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `X; measure Z` | raw CSS `xCheck2` | 2 | 2 | 2 | 1 | 2 | 3 | 10 | 4 |
| `X; measure Z` | surface d=2 | 2 | 2 | 2 | 4 | 3 | 7 | 28 | 10 |
| `X; measure Z` | surface d=3 | 2 | 2 | 2 | 12 | 4 | 16 | 78 | 26 |
| `X; measure Z` | surface d=4 | 2 | 2 | 2 | 24 | 5 | 29 | 154 | 50 |
| `X/Z; measure Z/Z` | toric d=2 | 4 | 4 | 4 | 8 | 6 | 14 | 64 | 18 |
| `X/Z; measure Z/Z` | toric d=3 | 4 | 4 | 4 | 18 | 8 | 26 | 133 | 38 |
| `X; measure Z` | HGP `[[8,1]]` | 2 | 2 | 2 | 7 | 3 | 10 | 47 | 16 |
| `X/Z; measure Z/Z` | lifted product `[[15,3]]` | 4 | 4 | 4 | 12 | 6 | 18 | 78 | 29 |
| `X/Z; measure Z/Z` | toy LP `[[15,2]]` | 4 | 4 | 4 | 6 | 6 | 12 | 52 | 14 |
| `X/Z; measure Z/Z` | BB `[[18,4]]` | 4 | 4 | 4 | 18 | 14 | 32 | 181 | 38 |
| `cx q[0],q[1]` | surface d=2 | 1 | 1 | 1 | 8 | 5 | 13 | 49 | 18 |
| `cx q[0],q[1]` | surface d=3 | 1 | 1 | 1 | 24 | 13 | 37 | 153 | 50 |
| `cx q[0],q[1]` | surface d=4 | 1 | 1 | 1 | 48 | 25 | 73 | 313 | 98 |
| 3-CX chain | surface d=2, 4 blocks | 3 | 3 | 3 | 16 | 15 | 31 | 103 | 36 |
| 3-CX chain | surface d=3, 4 blocks | 3 | 3 | 3 | 48 | 39 | 87 | 319 | 100 |
| 3-CX chain | surface d=4, 4 blocks | 3 | 3 | 3 | 96 | 75 | 171 | 651 | 196 |
| `cat_state_n4` | bare d=1 sanity | 8 | 8 | 8 | 0 | 8 | 8 | 8 | 4 |
| `ghz_n78` | bare d=1 sanity | 156 | 156 | 156 | 0 | 156 | 156 | 156 | 78 |

Larger direct QASMBench sources are also checked under the separated-bare setup. These rows
exercise parsing, allocation, ChainQ/LogicQ lowering, MixedIR lowering, QStab generation, and
QClifford extraction on nontrivial source circuits. Because each logical qubit is mapped to a
one-physical-qubit bare block, these rows are not code-distance scaling evidence:

| QASMBench source | Category/setup | QASM | LogicQ | MixedIR | Syn QStab | Logical QStab | Total QStab | QClifford | Width |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `cat_state_n4` | Cat/GHZ, bare d=1 | 8 | 8 | 8 | 0 | 8 | 8 | 8 | 4 |
| `hs4_n4` | Hidden shift, bare d=1 | 32 | 32 | 32 | 0 | 32 | 32 | 32 | 4 |
| `qec9xz_n17` | QEC, bare d=1 | 61 | 61 | 61 | 0 | 61 | 61 | 61 | 17 |
| `bv_n30` | Bernstein-Vazirani, bare d=1 | 107 | 107 | 107 | 0 | 107 | 107 | 107 | 30 |
| `cat_n65` | Cat/GHZ, bare d=1 | 130 | 130 | 130 | 0 | 130 | 130 | 130 | 65 |
| `ghz_n78` | Cat/GHZ, bare d=1 | 156 | 156 | 156 | 0 | 156 | 156 | 156 | 78 |

Direct MixedIR fixtures are also checked. `QASM = 0` and `LogicQ = 0` mean the input
starts at MixedIR, not that earlier layers compiled away:

| Example | Setup | QASM | LogicQ | MixedIR | Syn QStab | Logical QStab | Total QStab | QClifford | Width |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| H; S; X; CNOT; two PPMs | two bare blocks | 0 | 0 | 6 | 0 | 6 | 6 | 7 | 2 |
| batched CNOT; two Paulis; two PPMs | two bare blocks | 0 | 0 | 5 | 0 | 5 | 5 | 5 | 2 |

The current physical path includes exactly one stabilizer-extraction pass. It does not include
repeated syndrome rounds, decoder logic, fault-tolerance padding, or T-gate magic injection;
those remain explicit downstream obligations. A naive identity-incidence logical CX on
separated toric blocks is also a checked negative today: the compiler cannot prove that
incidence realizes the requested logical CNOT for that toric logical basis.

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

## One program at every level — the same program in each IR's syntax

The QASM front-end ingests real **QASMBench** circuits — e.g. `deutsch_n2`, `iswap_n2`
([Compiler/QASM/Benchmarks.lean](Compiler/QASM/Benchmarks.lean)) — and lowers them down the
tower. To see the lowering as *the same program rewritten in each language's own syntax*, here
is a minimal program — **flip a qubit, then read it out** — written out at every level (not as
compiler calls, but as the actual program value in each IR).

The values below are the **bare** single-qubit encoding `[[1,1,1]]`, where one logical qubit is
one physical qubit, so every box is exact; the lifted-product encoding follows at the end.

**The code — ChainQ syntax** (`ChainQ/Syntax.lean`, `inductive CodeDecl`). The logical qubit
lives in a declared code; for this trace a bare block, with a real lifted-product qLDPC code as
the encoded alternative:

```text
CodeDecl.css { n := 1, hx := [], hz := [] }          -- [[1,1,1]] bare block (the clean trace below)
CodeDecl.liftedProduct 3 [[[0], [1]]] 1 2            -- ℓ=3, A=[1,x] → an n=15 lifted-product qLDPC code
```

**Level 0 — OpenQASM 2 text** (the source program):

```text
qreg q[1];  creg c[1];
x q[0];
measure q[0] -> c[0];
```

**Level 1 — `QASMProgram`** (parsed; QASM-AST syntax):

```text
{ qregs  := [⟨"q", 1⟩],  cregs := [⟨"c", 1⟩],
  instrs := [ .x ⟨"q",0⟩,  .measure ⟨"q",0⟩ ⟨"c",0⟩ ] }
```

**Level 2 — `ChainQPrimProgram`** (allocated onto code block `box`, logical `d0`; named ChainQ
ops, `Compiler/ChainQ2Mixed`):

```text
[ .xGate "box" "d0",  .measure r [("box", "d0", .Z)] ]      -- r = the readout's classical var
```

**Level 3 — Mixed IR** (`List MixedInstr`; the same program in mixed-IR syntax):

```text
[ .pauli ⟨0,0⟩ .X,  .ppm (.meas r [(⟨0,0⟩, .Z)]) ]         -- X → applied logical Pauli; readout → native PPM
```

**Level 4 — the PPM fragment → lattice-surgery IR** (`Compiler.LS.Program`; the surgery IR owns
the measurement — on the bare block `Z̄` is physical `Z` on qubit 0):

```text
{ numQubits := 1,  ops := [ .meas (some ⟨0,0⟩) [(0, .Z)] ] }
```

**Level 5 — QStab** (physical stabilizer-measurement syntax; `QStab/StabilizerProgram.lean`):

```text
[ .X 0,  .bind (.prop (some ⟨0,0⟩) (ofString "Z")) ]
```

**Level 6 — QClifford** (the physical Clifford + measurement circuit; standard-Z extraction of
the `prop` via one ancilla):

```text
[ .X 0,  .prepZero 1,  .CNOT 0 1,  .meas 1 r ]              -- flip the data; read Z through ancilla 1
```

**The lifted-product encoding.** Replace `CodeDecl.css {…}` with the `liftedProduct` code above:
levels 0–3 are *unchanged* (they are code-agnostic logical IR), but `q0`'s logical `Z̄` is now the
code's high-weight logical operator, so the physical levels 4–6 **expand**. The verified
[end-to-end LOC table](#end-to-end-loc-by-layer) measures exactly this — e.g. `X/Z; measure Z/Z`
on a toy lifted product `[[15,2]]` is `4` MixedIR ops → `12` QStab instructions → `52` QClifford
gates over `14` physical qubits, all `#guard`-checked. (No physical LP values are hand-written
here; the table is the ground truth.)

## Concrete examples for each layer

Each block below is the **actual program / value in that layer's own syntax** — the data, not
the compiler functions or `by decide` tests. Every value is real and checked in the
repository; follow each link to its checked source.

### 1 · Logical & Physical — the shared vocabulary

Every IR addresses qubits the same way — a logical block + index — and the physical target uses
a dense 4-letter Pauli string:

```lean
⟨0, 0⟩                 -- a LQubit: logical qubit 0 of block 0  (Logical/Basic.lean)
[.Z, .Z, .I]           -- a physical Pauli string, i.e. "ZZI"   (Physical/Basic.lean)
```

→ [Logical/](Logical/README.md) · [Physical/](Physical/README.md)

### 2 · ChainQ — declare a QEC code family

Code families are written in ChainQ syntax (`inductive CodeDecl`); each elaborates and
type-checks (shape, CSS commutation `H_X·H_Zᵀ = 0`, logical-class membership) into a
validity-carrying `CheckedCSSCode`:

```lean
CodeDecl.surface 3
CodeDecl.toric 2
CodeDecl.bb 3 3 [(0, 0), (1, 0), (0, 2)] [(0, 0), (2, 0), (0, 1)]
CodeDecl.liftedProduct 3 [[[0], [1]]] 1 2
```

→ [ChainQ/Syntax.lean](ChainQ/Syntax.lean) · [ChainQ/](ChainQ/README.md)

### 3 · TypeChecker — logical measurement targets & the capability that admits them

The distinctive judgment is a **proof-carrying capability matcher**: a cross-code joint
measurement `Z̄ ⊗ Z̄` is rejected unless an installed adapter capability recomputes a valid
merged-code certificate. The programs are the measurement targets; the capability is its own
value:

```lean
[(⟨0,0⟩, .Z)]                       -- native single-block Z̄ measurement  (accepted)
[(⟨0,0⟩, .Z), (⟨1,0⟩, .Z)]          -- cross-code joint Z̄⊗Z̄              (REJECTED with no capability)
{ kind := .adapterPPM, blocks := [0, 1], ancN := 0,            -- the adapter capability that ADMITS it:
  connStab := [[false, false, false, false, true, true, false, false]] }
```

→ [TypeChecker/Judgment/PPM/Examples.lean](TypeChecker/Judgment/PPM/Examples.lean) · [TypeChecker/](TypeChecker/README.md)

### 4 · Compiler / Mixed IR — a source program and its lowering

A logical source program (`List LogicalOp`) lowers to Mixed IR (`List MixedInstr`). `H; S`
becomes two direct transversals (and `execMixed`-runs to the same state as the ideal simulator
— exact-operational equality):

```lean
[ .hGate ⟨0,0⟩, .sGate ⟨0,0⟩ ]                          -- source program: List LogicalOp
[ .transversal 0 [[false, true], [true, false]]         -- Mixed IR: H as the X↔Z transversal
, .transversal 0 [[true, true], [false, true]] ]        --           S as the X↦Y transversal
```

→ [Compiler/Demo/Contract.lean](Compiler/Demo/Contract.lean) · [Compiler/Mixed/](Compiler/Mixed/README.md)

### 5 · ChainQ2Mixed — request ≠ realization (transversal CNOT)

The front-end separates *what* a logical op requests from *how* it is realized. A transversal
logical CNOT carries its physical incidence; a zero incidence that still claims a logical CNOT
is rejected (the lifted symplectic map would induce the identity, not the CNOT):

```lean
.transversalCNOT { control := ⟨0,0⟩, target := ⟨1,0⟩, incidence := [[true]] }    -- accepted
.transversalBatch { controlBlock := 0, targetBlock := 1,                           -- REJECTED:
                    incidence := [[false]], logicalIncidence := [[true]] }         -- zero incidence ≠ CNOT
```

→ [Compiler/ChainQ2Mixed/Primitive.lean](Compiler/ChainQ2Mixed/Primitive.lean) · [Compiler/ChainQ2Mixed/](Compiler/ChainQ2Mixed/README.md)

### 6 · PPR — logical Pauli-product rotations

The `L_PPR` spec: a program is a sequence of `exp(i φ P)` rotations, each an angle + a Pauli
product. This program has T-count 2:

```lean
⟨⟨false, .piEighth⟩,  [(⟨0,0⟩, .Z)]⟩                       -- a T rotation on qubit 0
⟨⟨false, .piQuarter⟩, [(⟨0,0⟩, .Z)]⟩                       -- an S rotation on qubit 0
⟨⟨false, .piEighth⟩,  [(⟨0,0⟩, .Z), (⟨0,1⟩, .Z)]⟩          -- a ZZ rotation on qubits 0,1
-- the program is the list  [ T(q0), S(q0), ZZ(q0,q1) ]
```

→ [PPR/Syntax.lean](PPR/Syntax.lean) · [PPR/](PPR/README.md)

### 7 · PPM — adaptive Pauli-product measurement (QMeas)

The `L_PPM` measurement language; a measurement target is a one- or two-body logical
observable (the natively lattice-surgery-realizable alphabet):

```lean
[(dataQ 0, .Z), (ancQ 0, .X)]       -- a valid two-body observable
[(dataQ 0, .X)]                      -- a valid one-body observable
[(dataQ 0, .Z), (dataQ 0, .X)]       -- REJECTED: a repeated qubit
```

→ [PPM/Syntax.lean](PPM/Syntax.lean) · [PPM/](PPM/README.md)

### 8 · Code switching — a transparent cross-code coercion

Encoding a bare qubit into the `[[3,1,1]]` repetition code is a switch certificate that
**preserves the logical operators** (it induces `X̄ = XXX`); a degenerate all-zero map is
rejected. The certificate is its own value — a kind + the symplectic map `f`:

```lean
{ kind := .gaugeFix,                                      -- the switch certificate, with map f:
  f := [[true,  true,  true,  false, false, false],       --   X̄ ↦ XXX
        [false, false, false, true,  false, false]] }     --   Z̄ ↦ ZII
-- induced logical X̄ = [[true, true, true, false, false, false]]   (= XXX)
```

→ [TypeChecker/Judgment/Switch/Examples.lean](TypeChecker/Judgment/Switch/Examples.lean) · [Compiler/CodeSwitch/](Compiler/CodeSwitch/README.md)

### 9 · MagicQ — magic-state protocols

A magic-state protocol is a list of `ProtocolOp`s. Here is the standard 15-to-1 distillation
(15 `T` inputs → one output) in MagicQ syntax — the non-Pauli Bravyi–Kitaev A-type syndrome
stays an explicit deferred obligation, not claimed proven:

```lean
{ name := "rm15_to_1",
  ops  := <15 × .inject .supplied .T …> ++                            -- 15 supplied noisy T inputs
          [ .distill15To1 (List.range 15) 15 15 (.external "RM15-[[15,1,3]]")
              rm15OutQuality ["rm15.z-syndrome", "rm15.eta"],           -- measure the RM-15 syndrome
            .postselect (.syndromeEq "rm15.eta" false),                 -- keep iff η = 0
            .output 15 ] }                                              -- return the distilled T
```

→ [MagicQ/Tests.lean](MagicQ/Tests.lean) · [MagicQ/](MagicQ/README.md)

### 10 · QStab — physical stabilizer-measurement dataflow

The `L_QStab` target is an SSA-style classical dataflow over physical Pauli measurements
(`.prop`) and classical parities (`.parity`). A program reads like this — `parity` detectors
are syndromes, the last `parity` is the logical readout:

```lean
[ .prop (some ⟨0,0⟩) (ofString "ZZI"),   -- c0
  .prop (some ⟨0,1⟩) (ofString "IZZ"),   -- c1
  .prop (some ⟨1,0⟩) (ofString "ZZI"),   -- c2
  .parity [0, 2],                          -- d0 = c0 ⊕ c2   (a syndrome detector)
  .prop (some ⟨1,1⟩) (ofString "IZZ"),   -- c3
  .parity [1, 4],                          -- d1 = c1 ⊕ c3
  .prop none (ofString "ZZZ"),            -- c4
  .parity [6] ]                            -- o0 = c4         (the logical output)
```

→ [QStab/Semantics.lean](QStab/Semantics.lean) · [QStab/](QStab/README.md)

### 11 · QClifford — the physical Clifford + measurement target

The terminal `L_QClifford` IR: a circuit is a list of physical Clifford gates, Z-basis
measurements, and classically-conditioned Pauli corrections. E.g. `CNOT(0,1)` realized from a
`CZ` (3 gates, 1 two-qubit):

```lean
[ .H 1, .CZ 0 1, .H 1 ]            -- CNOT(0,1) = H · CZ · H
```

→ [QClifford/Syntax.lean](QClifford/Syntax.lean) · [QClifford/](QClifford/README.md)

### 12 · QStab → QClifford — the syndrome-extraction pass

Each physical stabilizer `.prop` is extracted by a chosen scheme (standard / destructive /
Shor / Knill / flag). A standard-Z measurement of `ZZ` on data qubits `{0,1}`, reading into
result var 7, extracts to this QClifford circuit:

```lean
[ .prepZero 3, .CNOT 1 3, .CNOT 0 3, .meas 3 7 ]   -- fresh ancilla 3, two CNOTs from the data, one measurement
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
