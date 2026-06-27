# LogicQ

**LogicQ is a verified compilation pipeline — a "quantum CompCert" — for fault-tolerant
quantum programming, implemented in Lean 4.**

It compiles a program written in a high-level language with a **chain-complex type system**
down to a concrete physical Clifford + measurement circuit, through a stack of intermediate
representations (IRs). Every level has

1. a **syntax** in standard BNF form,
2. a precise **semantics**, and
3. (the goal) a machine-checked **semantics-preservation proof** for the pass that lowers it.

> **Methodology — languages first.** Each IR level's syntax + semantics is fixed as an
> independent, self-contained Lean specification *before* the inter-level compiler passes are
> built. This README documents the **BNF of every level, with examples.**

---

## The pipeline

```
  ChainQ  ──►  PPR  ──►  PPM (QMeas)  ──►  Lattice Surgery  ──►  QStab  ──►  QClifford
  typed        Pauli       measurement       patch merges /        physical     physical
  front end    rotations   -based control    splits (surgery)      stabilizer   Clifford
  (codes +     exp(iφP)    (adaptive         realizing logical     readout      circuit
  logical ops)             frame updates)    measurements          Prop/Parity  (target)
   └────────────── LOGICAL qubits ─────────────┘   └──────── PHYSICAL qubits ────────┘
```

| Level | Role | Qubits | Status | Source |
|---|---|---|---|---|
| **ChainQ — code types** | declare QEC codes (chain complex / CSS / stabilizer) | — | ✅ implemented | [ChainQ/](ChainQ/) |
| **ChainQ — logical program + MagicQ** | logical FT ops + post-selected protocols | logical | 📋 planned | [DESIGN.md](DESIGN.md) |
| **PPR** | Pauli-product rotations `exp(iφP)` | logical | ✅ implemented | [PPR/](PPR/) |
| **PPM (QMeas)** | measurement-based control + Pauli frame | logical | ✅ implemented | [PPM/](PPM/) |
| **Lattice Surgery** | patch merges/splits realizing measurements | logical→physical | 📋 planned | [DESIGN.md](DESIGN.md) |
| **QStab** | physical stabilizer measurements + parities | physical | ✅ implemented | [QStab/](QStab/) |
| **QClifford** | physical Clifford + measurement circuit (target) | physical | ✅ implemented | [QClifford/](QClifford/) |

Shared vocabulary: [Logical.lean](Logical.lean) (`BlockId`, `LQubit = ⟨block, index⟩`) and
[Physical.lean](Physical.lean) (`PQubit`, 4-element `Pauli`).

*Status legend: ✅ = syntax **and** semantics built and machine-checked in Lean (sorry-free);
📋 = syntax/semantics designed (see [DESIGN.md](DESIGN.md)), implementation pending. The verified
inter-level compiler **passes** are the next phase after the spec phase completes.*

---

## Shared vocabulary

```
BlockId ::= Nat                          -- a declared logical block (surface q1, q2, t0, …)
LQubit  ::= '⟨' BlockId ',' Nat '⟩'      -- a LOGICAL qubit: q1[i] = ⟨q1, i⟩   (PPR, PPM)
PQubit  ::= Nat                          -- a PHYSICAL qubit index               (QStab, QClifford)
Pauli   ::= 'I' | 'X' | 'Y' | 'Z'        -- single-qubit Pauli
```

LogicQ is split at the dashed line above: **PPR and PPM operate on logical qubits** (the logical
qubits of declared code blocks); **physical qubits appear only at QStab / QClifford**, after lowering.

---

## Level: ChainQ — code types ✅

The front-end **type system**: a QEC code is declared in one of three kinds, each with a
**decidable well-typedness** judgement. The headline theorem `chainComplex_css` proves the type
system is *sound* — a well-typed chain complex elaborates to a genuine (commuting) CSS code.

### BNF

```
CodeKind   ::= 'CellComplex' 'over' 'Z2' | 'StabilizerCode' | 'CSSCode'

CellComplex ::= 'cells' '{' CellGroup* '}'
                'boundary' '{' BdyEqn* '}'
                'css' '{' 'hx' '=' MatExpr ';' 'hz' '=' MatExpr ';' '}'
BdyEqn     ::= ('d2' | 'd1') '(' CellRef ')' '=' BdySum ';'
BdySum     ::= CellRef ('+' CellRef)*                      -- formal Z2 sum
MatExpr    ::= 'matrix' '(' ('d2'|'d1') ')' | 'transpose' '(' MatExpr ')'

StabilizerCode ::= 'n' '=' Nat ';'
                   'generators' '{' (Id '=' PauliLit ';')* '}'
                   ('logical_z' '{' (Id '=' PauliLit ';')* '}')?

CSSCode    ::= 'n' '=' Nat ';' 'hx' '=' BoolMat ';' 'hz' '=' BoolMat ';'

PauliLit   ::= ('I'|'X'|'Y'|'Z')+
```

**Well-typedness.** A `CellComplex` (`C₂ —∂₂→ C₁ —∂₁→ C₀`) is well-typed iff the chain-complex law
`∂₁∘∂₂ = 0` holds; it elaborates to a CSS code `hx := matrix(d2)`, `hz := transpose(matrix(d1))`.
A `CSSCode` is well-typed iff `Hₓ·Hᵤᵀ = 0`. A `StabilizerCode` is well-typed iff its generators
pairwise commute. (See `ChainQ.chainComplex_css`, `CSSCode.valid`, `StabilizerCode.valid`.)

### Examples

```python
# A square plaquette — the smallest surface-code cell, as a chain complex over Z2
code square as CellComplex over Z2 {
  cells    { f0;  e0; e1; e2; e3;  v0; v1; v2; v3 }       # 1 face, 4 edges (qubits), 4 vertices
  boundary {
    d2(f0) = e0 + e1 + e2 + e3;                           # the XXXX plaquette
    d1(e0) = v0 + v1;  d1(e1) = v1 + v2;
    d1(e2) = v2 + v3;  d1(e3) = v3 + v0;
  }
  css { hx = matrix(d2); hz = transpose(matrix(d1)); }     # ∂₁∘∂₂ = 0  ⟹  Hₓ·Hᵤᵀ = 0  ✓
}

# The five-qubit perfect [[5,1,3]] code, as explicit stabilizers
code five_qubit as StabilizerCode {
  n = 5;
  generators { S0 = "XZZXI"; S1 = "IXZZX"; S2 = "XIXZZ"; S3 = "ZXIXZ"; }
  logical_z  { LZ0 = "ZZZZZ"; }                            # commutes with all Sᵢ  ✓
}
```

Both are machine-checked in Lean (`ChainQ.square`, `ChainQ.fiveQubit`) — `decide` verifies the chain
law / commutation and that `ZZZZZ` is a genuine logical operator. Backed by
[ChainQ/ChainComplex.lean](ChainQ/ChainComplex.lean), [ChainQ/Code.lean](ChainQ/Code.lean),
[ChainQ/GF2.lean](ChainQ/GF2.lean).

---

## Level: ChainQ — logical program + MagicQ 📋

The user-facing logical language: declare code **blocks**, apply logical FT operations, and express
post-selected magic-state protocols (**MagicQ**). Each statement elaborates to a `PPR` rotation.

### BNF

```
Prog      ::= Decl*
Decl      ::= CodeKind Id '[' KV* ']'                      -- surface q1 [n=40, k=1, d=5]
            | CVar '=' LogicOp
            | 'InjectT' QubitRef ',' Handle
            | Handle '=' ProtocolCall
LogicOp   ::= 'LogicH' QubitRef | 'LogicS' QubitRef | 'LogicT' QubitRef
            | 'LogicCNOT' QubitRef ',' QubitRef
            | 'LogicMeasure' QubitRef | 'LogicProp' PauliLit
QubitRef  ::= Id '[' Nat ']'                               -- q1[0]

Protocol  ::= 'protocol' Id '(' Param* ')' ':'
              'Repeat' ':' Stmt* 'Success' '=' BoolExpr 'Until' 'Success' 'return' Handle?
```

### Examples

```python
surface q1 [n=40, k=1, d=5]      # data block (distance-5 surface code)
surface q2 [n=40, k=1, d=5]      # data block
surface t0 [n=84, k=1, d=7]      # magic-state ancilla block

q1[0] = LogicH q1[0]
t0    = Distill15to1_T[d=25]     # a MagicQ protocol factory call → magic handle
InjectT q1[0], t0
q2[1] = LogicCNOT q1[0], q2[1]
c1    = LogicMeasure q1[0]
c2    = LogicMeasure q2[1]
```

```python
# MagicQ: 15-to-1 T-state distillation (Bravyi–Haah), a post-selected Repeat…Until protocol
protocol Distill15to1_T(surface f, int d):
  Repeat:
      c_x1 = LogicProp IIIIIIIXXXXXXXX
      # … 13 more logical-Pauli checks …
      c_z34 = LogicProp IIZIIIZIIIZIIIZ
      Success = c_x1 == 0 && c_x2 == 0 && c_x3 == 0 && c_x4 == 0 &&
                c_z1 == 0 && c_z2 == 0 && /* … */ c_z34 == 0
      Until Success
      return
```

Semantics (planned): a logical program denotes a logical channel (elaboration to `PPR`); a MagicQ
protocol denotes a **post-selected channel** conditioned on `Success`. See [DESIGN.md](DESIGN.md) §L_FE.

---

## Level: PPR — Pauli-Product Rotation IR ✅

Litinski-style rotations: every logical instruction becomes a rotation `exp(iφP)` of a logical Pauli
string `P` by a phase `φ ∈ ±{π, π/2, π/4, π/8}`. The `π/8` count is exactly the **T-count**.

### BNF

```
Pauli       ::= 'X' | 'Y' | 'Z'                            -- I = absence of a factor
PauliString ::= ( LQubit '↦' Pauli )*                      -- a logical Pauli product P (sparse)
Angle       ::= 'π' | 'π/2' | 'π/4' | 'π/8'
Phase       ::= ('+' | '-') Angle                          -- φ = ± Angle
Rot         ::= Phase '·' PauliString                      -- exp(i φ P)
RotProg     ::= Rot*                                       -- applied left to right
```

**Semantics.** `rotOf φ M = cos φ · 1 + (i · sin φ) · M`, where a Pauli string `P` denotes a monomial
complex matrix `M`; a program denotes the matrix **product** of its rotations. Law:
`denote (p ++ q) = denote q · denote p`. (`π/2` → Pauli, `π/4` → Clifford/S-type, `π/8` → T-type.)

### Examples

```
+π/8 · (q1[0] ↦ Z)                  -- a logical T gate on q1[0]:  exp(i π/8 Z)
+π/4 · (q1[0] ↦ Z)                  -- a logical S gate on q1[0]
+π/8 · (q1[0] ↦ Z, q1[1] ↦ Z)      -- a two-qubit exp(i π/8 Z⊗Z) over {q1[0], q1[1]}

[ +π/8·Z₀ , +π/4·Z₀ , +π/8·Z₀Z₁ ]   -- a RotProg with T-count = 2
```

Backed by [PPR/Syntax.lean](PPR/Syntax.lean) (`rotT`, `rotS`, `rotZZ`, `tCount`) and the Mathlib-based
denotation in [PPR/Semantics.lean](PPR/Semantics.lean) (`rotOf`, `RotProg.denote`, `denote_append`).

---

## Level: PPM — QMeas measurement-based IR ✅

A measurement-only language where logical instructions become Pauli measurements with adaptive
**Pauli-frame** corrections. The distinguishing control primitive is the adaptive conditional
`if r = +1 then S₁ else S₂`. Maps one-to-one to native lattice-surgery operations.

### BNF

```
Sign     ::= '+1' | '-1'
PLetter  ::= 'X' | 'Y' | 'Z'
MTarget  ::= ( LQubit '↦' PLetter )*                       -- a logical Pauli product, M_P(q⃗)

Stmt  S  ::= r ':=' 'M' MTarget                            -- r := M_P(q⃗)  (Pauli measurement)
           | 'frame' PLetter '(' LQubit ')'                -- frame_X/Y/Z(q)  (record byproduct)
           | 'discard' LQubit
           | 'if' r '=' '+1' 'then' S 'else' S             -- adaptive conditional
           | 'for' Nat 'do' S                              -- bounded loop
           | 'skip'
           | S ';;' S                                      -- sequencing
           | 'abort'                                       -- stuck terminal (post-selection)
```

**Semantics.** A small-step operational semantics over configurations `⟨ρ, σ, F, S⟩` (quantum state,
classical store, Pauli frame, program). The frame **composes** on update (so `Z` then `X` = `Y`);
`abort` is a **stuck terminal**, partitioning runs into *accepted* (`skip`) and *rejected* (`abort`).

### Examples

```python
# Hadamard gadget (Litinski lattice-surgery form): data q1[0], ancilla a1[0]=⟨1,0⟩ in |0⟩
r  := M_{ZX}(q1[0], a1[0]);
r' := M_X(q1[0]);
if r  = +1 then skip else frame_Z(a1[0]);     # adaptive byproduct on the ancilla
if r' = +1 then skip else frame_X(a1[0]);
discard q1[0]
#  outcome table (r, r') → byproduct:  (+,+)→I  (+,-)→X  (-,+)→Z  (-,-)→Y      (machine-checked)

# CNOT gadget: control q1[0], target q1[1], ancilla a1[0]
r  := M_{ZZ}(q1[0], a1[0]);  r' := M_{XX}(a1[0], q1[1]);  r'' := M_Z(a1[0]);
if r' = +1 then skip else frame_Z(q1[0]);
if r  = +1 then (if r''=+1 then skip else frame_X(q1[1]))   # encodes  r ≠ r''
            else (if r''=+1 then frame_X(q1[1]) else skip);
discard a1[0]

# Post-selection check (cultivation): accept on +1, abort on -1
r := M_Z(q);  if r = +1 then skip else abort
```

The Hadamard gadget's full byproduct table is **proven from the small-step rules** (`PPM.progH_frame`,
all four branches). Backed by [PPM/Syntax.lean](PPM/Syntax.lean) (`progH`, `progS`, `progCNOT`,
`checkPlus`) and [PPM/Semantics.lean](PPM/Semantics.lean) (`Step`, `Steps`, `abort_stuck`).

---

## Level: Lattice Surgery 📋

The spacetime realization of multi-patch logical Pauli measurements as code-patch **merges/splits**
on a 3D pipe diagram — the bridge from logical PPM measurements to physical QStab schedules.

### BNF (sketch)

```
LSProgram  ::= LSNode*
LSNode     ::= 'Gadget' SurgeryGadget                      -- one merge/split on a patch pair
             | 'weldK' LSNode LSNode | 'weldI' LSNode LSNode
             | 'rotLaS' LSNode
SurgeryGadget ::= '{' 'target_pauli' '=' PauliLit ','
                      'merged_hx' '=' MatExpr ',' 'merged_hz' '=' MatExpr ','
                      'span_witness' '=' Proof '}'
LaSre      ::= Nat '→' Nat '→' Nat '→' Bool                -- a 3D pipe diagram (correlation surface)
```

Semantics (planned): a merge denotes its merged stabilizer group (`measureChecks`); validity is the
correlation-surface even-parity condition. This layer's verified gadgets are re-exported from
FormalRV's `QEC.LatticeSurgery`. See [DESIGN.md](DESIGN.md) §L_LS.

---

## Level: QStab — physical stabilizer-measurement IR ✅

A dataflow of **physical** Pauli measurements (`Prop[r,s] P`) and classical **parities**
(`Parity c…`), binding classical variables in program order — the syndrome / logical-readout program.

### BNF

```
QVar      ::= c0 | c1 | …                                  -- classical variable (SSA: stmt i binds var i)
PauliStr  ::= ('I'|'X'|'Y'|'Z')+                           -- dense physical Pauli, e.g. ZZI
Sched     ::= '[' 'r' '=' Nat ',' 's' '=' Nat ']'          -- round, slot

Stmt      ::= QVar '=' 'Prop' Sched? PauliStr              -- physical Pauli measurement
            | QVar '=' 'Parity' QVar+                       -- classical XOR of earlier outcomes
Prog      ::= Stmt*
```

**Semantics.** A classical dataflow `eval`: a `Prop` variable is its measurement outcome, a `Parity`
is the XOR of the variables it references. Well-formedness rejects forward references.

### Example

```python
c0 = Prop[r=0, s=0] ZZI       # measure physical ZZI at round 0, slot 0
c1 = Prop[r=0, s=1] IZZ
c2 = Prop[r=1, s=0] ZZI
d0 = Parity c0 c2             # a syndrome bit (XOR)
c3 = Prop[r=1, s=1] IZZ
d1 = Parity c1 c3
c4 = Prop ZZZ                 # scheduling coordinates optional
o0 = Parity c4                # a decoded logical output bit
```

Machine-checked: `QStab.progReadout` (this distance-3 readout) evaluates correctly under `eval` —
a flipped check flips its syndrome but not the logical output. Backed by
[QStab/Syntax.lean](QStab/Syntax.lean), [QStab/Semantics.lean](QStab/Semantics.lean).

---

## Level: QClifford — final target ✅

The executable artifact: a circuit of **physical** Clifford gates, `Z`-basis measurements, and
classically-conditioned (feed-forward) Pauli corrections.

### BNF

```
Gate     ::= 'H' q | 'S' q | 'X' q | 'Z' q                 -- single-qubit Clifford
           | 'CNOT' c t | 'CZ' a b                          -- two-qubit Clifford
           | 'Meas' q '->' r                                -- Z-basis measurement → classical bit r
           | 'If' r 'then' Pauli q                          -- feed-forward Pauli correction
Circuit  ::= Gate*
```

**Semantics.** A parametric operational semantics: a `Host St` supplies the gate actions and a
`Z`-measurement; `run` threads `(state, store)` through the circuit. Composition law:
`run (c₁ ++ c₂) = run c₂` from the output of `run c₁` (`run_append`). The host `St` is instantiated
later with a stabilizer tableau (Mathlib-free) or a density matrix.

### Example

```python
# CNOT(0,1) realized from CZ:  H 1 ; CZ 0 1 ; H 1
H 1;  CZ 0 1;  H 1

# a measurement with feed-forward correction
Meas 0 -> r5;  If r5 then Z 1
```

Backed by [QClifford/Syntax.lean](QClifford/Syntax.lean) (`Gate`, `Circuit`, `cnotFromCZ`, resource
counts) and [QClifford/Semantics.lean](QClifford/Semantics.lean) (`Host`, `run`, `run_append`).

---

## Building

```bash
lake exe cache get      # one-time: prebuilt Mathlib oleans (only PPR semantics needs Mathlib)
lake build              # builds the whole library
```

Pinned to `leanprover/lean4:v4.29.1` + `mathlib @ v4.29.1` (matching FormalRV). Most levels are
Mathlib-free pure `Bool`/`List`/`Nat`; only `PPR/Semantics.lean` imports Mathlib (for the
complex-matrix denotation of `exp(iφP)`).

## Design & status

The full architecture, the CompCert-style correctness strategy, and the phased roadmap are in
**[DESIGN.md](DESIGN.md)**. A companion **type checker** for *legal logical operations* (which
transversal gates / code-switching moves are well-formed, e.g. whether a PPM between a surface-code
and an LP-code logical qubit is possible) is being developed under [TypeChecker/](TypeChecker/).

This project reuses and is informed by the [FormalRV](../FormalRV) framework.
