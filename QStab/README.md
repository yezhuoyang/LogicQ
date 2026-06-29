# QStab

> The physical stabilizer-measurement IR (level `L_QStab`): a classical dataflow of physical Pauli-product measurements and parities.

`QStab` is the **physical target** the LogicQ pipeline lowers toward (front-end ChainQ code families -> TypeChecker legality -> Compiler Mixed IR -> PPM/LS surgery edges -> **QStab** -> QClifford). A QStab `Prog` is an SSA-style dataflow: each statement binds the next classical variable `c0, c1, …`, where a `prop` is a physical Pauli measurement (`Prop[r,s] P`) and a `parity` is the classical XOR of earlier outcomes (syndromes / logical-readout bits). `eval` computes those classical bits from the `±1` measurement outcomes; the quantum back-action is intentionally outside this small semantics. The `Mixed`/`PPM` edge feeds in via `ppmMeasToQStab`, and `Compiler.QStab2QClifford` lowers this dataflow out to QClifford using explicit syndrome-extraction schemes.

## What's here

| Module | Role |
|---|---|
| [Basic.lean](Basic.lean) | Umbrella import for the whole QStab layer |
| [Syntax.lean](Syntax.lean) | Dense `PauliString`, `Sched`, `Stmt` (`prop`/`parity`), `Prog`, and well-formedness `Prog.wf` |
| [Semantics.lean](Semantics.lean) | Classical dataflow `eval`/`evalVar` over `Bool` outcomes + `eval_length` |
| [StabilizerProgram.lean](StabilizerProgram.lean) | Richer `StabilizerInstr` shell (preps/Cliffords/`ifPauli`) projecting to the checked dataflow |
| [SparsePauli.lean](SparsePauli.lean) | Explicit indexed `SparsePauli` + CHECKED densification `toDense?` |

## Key definitions

```lean
/-- A QStab statement; each binds the next classical variable. -/
inductive Stmt
  | prop   (sched : Option Sched) (P : PauliString)
  | parity (srcs : List QVar)
  deriving DecidableEq, Repr, Inhabited
```
from [Syntax.lean](Syntax.lean); `abbrev Prog := List Stmt`, `abbrev PauliString := List Pauli`, `abbrev QVar := Nat`.

```lean
/-- **Program well-formedness**: variables bind sequentially from `c0`, and
    every parity references only already-bound variables. -/
def Prog.wf (p : Prog) : Bool := Prog.wfFrom 0 p
```
from [Syntax.lean](Syntax.lean) (rejects forward references).

```lean
/-- The value of every bound variable, in program order, given the `prop`
    outcomes `o` (indexed by `prop`-occurrence). -/
def eval (p : Prog) (o : Nat → Bool) : List Bool := evalAux p 0 o []
```
from [Semantics.lean](Semantics.lean), with `evalVar` and the proved `theorem eval_length (p : Prog) (o : Nat → Bool) : (eval p o).length = p.length`.

```lean
/-- **CHECKED densification of a MEASUREMENT** sparse Pauli to a dense `PauliString` over a
    declared `numQubits`-qubit device. ... -/
def SparsePauli.toDense? (numQubits : Nat) (P : SparsePauli) :
    Except SparsePauliError PauliString
```
from [SparsePauli.lean](SparsePauli.lean) — refuses empty / identity / duplicate-qubit / out-of-range operators (never silently identity-defaults).

```lean
inductive StabilizerInstr
  | bind     (stmt : Stmt)
  | prepZero (q : PQubit)
  | H        (q : PQubit)
  | ifPauli  (src : QVar) (p : Pauli) (q : PQubit)
  ...
```
from [StabilizerProgram.lean](StabilizerProgram.lean) — `.bind` is the only variable-binding instruction; `StabilizerProg.dataflow` projects to the checked `Prog` semantics.

## Example

`progReadout` (defined in [Syntax.lean:80](Syntax.lean#L80)) is itself a QStab `Prog`: it
measures `ZZI`/`IZZ` over two rounds and forms syndrome parities `d0, d1` plus a logical
output `o0`. As pure QStab syntax it is the list of statements (binding `c0..c4`, then
`d0, d1, o0`):

```lean
-- progReadout : Prog  (a distance-3 repetition-style syndrome + logical readout)
[ .prop (some ⟨0, 0⟩) (ofString "ZZI"),   -- c0  (round 0, check ZZI)
  .prop (some ⟨0, 1⟩) (ofString "IZZ"),   -- c1  (round 0, check IZZ)
  .prop (some ⟨1, 0⟩) (ofString "ZZI"),   -- c2  (round 1, check ZZI)
  .parity [0, 2],                          -- d0 = c0 ⊕ c2   (syndrome bit, var 3)
  .prop (some ⟨1, 1⟩) (ofString "IZZ"),   -- c3  (round 1, check IZZ)
  .parity [1, 4],                          -- d1 = c1 ⊕ c3   (syndrome bit, var 5)
  .prop none (ofString "ZZZ"),            -- c4  (logical Z readout)
  .parity [6] ]                            -- o0 = c4         (logical output, var 7)
```

Evaluated on the outcome vector that flips only the first physical measurement
(`c0 = -1`, all others `+1`), the bound variables come out as:

```lean
-- A single flipped check c0 = -1 flips the syndrome d0 = c0 ⊕ c2 …
-- d0 (var 3)  =  true        -- flipped
-- o0 (var 7)  =  false       -- logical output o0 = c4 untouched
```

These values, from [Semantics.lean:56](Semantics.lean#L56), confirm that flipping the first
physical measurement flips the corresponding syndrome bit but not the final logical-output
parity.

## Status & scope

Using the [CONTRACT.md](../Compiler/CONTRACT.md) tiers (P proved theorem, D `by decide` test, A documented assumption, M missing/planned):

- **P** — Syntax/`Prog`/`Stmt` and the checker `Prog.wf` (forward-reference rejection); the classical dataflow `eval`/`evalVar`; `eval_length` / `evalAux_length` are proved theorems. The QStab2QClifford trace-correctness bridge to `QStab.evalVar` is proved in the consuming pass (see [Compiler/QStab2QClifford](../Compiler/QStab2QClifford/README.md)).
- **D** — `progReadout.wf`, the `eval`/`evalVar` readout runs, `exampleStabilizerProg`, and the `SparsePauli.toDense?` / `wfMeas` acceptance & rejection cases are executable `by decide` instances.
- **A / M (DEFERRED)** — This layer is **classical-dataflow only**. The quantum side — how `prop` outcomes arise from, and back-act on, the physical stabilizer state (the `proj`-style channel, LeanQEC's Heisenberg layer) — is **out of scope here**. Fault tolerance, code distance, decoder behaviour, verifier/flag weight bounds, hook detection, and any Stim/DEM export are explicitly **deferred / not proved**. Soundness results in the consuming passes are typically `propext`-clean, not "axiom-free".

Do not read the proved classical-dataflow guarantees as channel-correctness or fault-tolerance claims; those remain deferred.

## See also

- Parent: [Compiler README](../Compiler/README.md) and the [repo root README](../README.md)
- Compiler contract: [Compiler/CONTRACT.md](../Compiler/CONTRACT.md) (stage 6 = QStab)
- Downstream lowering: [Compiler/QStab2QClifford](../Compiler/QStab2QClifford/README.md) and the [QClifford](../QClifford/README.md) physical target
