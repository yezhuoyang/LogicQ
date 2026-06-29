# TypeChecker/Judgment

> The per-operation legality judgments of the LogicQ type checker.

This folder holds the static judgments that decide whether one logical operation is
*legal* on a given typed code block. It sits in the legality layer of the LogicQ stack
(front-end ChainQ code families -> **TypeChecker legality** -> Compiler Mixed IR -> ...
-> QStab/QClifford physical target): each judgment consumes a `TypedEnv` and either
produces a typed certificate of legality or a `TypeError`. The four modules here are
thin **aggregators** (M20 strict-folder-ownership refactor) that re-export the real
definitions from their same-named subfolders, so `import TypeChecker.Judgment.X`
keeps resolving the original names.

## What's here

| Module | Role |
| --- | --- |
| [Transversal.lean](Transversal.lean) | Aggregator: re-exports `checkLogicalAutomorphism` / `checkTransversal` / `checkTransversalCNOT` (binary-symplectic local gates + automorphisms + inter-block CNOT) from [Transversal/](Transversal/README.md). |
| [Switch.lean](Switch.lean) | Aggregator: re-exports `checkSwitch` / `SwitchCert` / `toTargetBlock?` (code switching as a typed coercion) from [Switch/](Switch/README.md). |
| [PPM.lean](PPM.lean) | Aggregator: re-exports `checkPPM` / `TypedPPM` / `checkPPMFromEnv` (cross-code logical-Pauli measurement capability matcher) from [PPM/](PPM/README.md). |
| [PPMProgram.lean](PPMProgram.lean) | Aggregator: re-exports `PPMState` / `checkPPMProgram` + soundness theorems (well-formedness of a whole PPM statement) from [PPMProgram/](PPMProgram/README.md). |

Each `.lean` file in this folder is only a list of `import`s; all data, checkers,
examples, and theorems live one directory down.

## Key definitions

The exported checkers (verbatim signatures from the owning subfolders):

```lean
def checkTransversal (Γ : TypedEnv) (b : BlockId) (g : BoolMat) :
    Except TypeError TypedTransversal
```
([Transversal/Check.lean](Transversal/Check.lean))

```lean
def checkSwitch (Γ : TypedEnv) (b : BlockId) (D : TypedBlock) (cert : SwitchCert) :
    Except TypeError (TypedEnv × TypedSwitch)
```
([Switch/Check.lean](Switch/Check.lean))

```lean
def checkPPM (Γ : TypedEnv) (caps : List Capability) (P : PPM.MTarget) :
    Except TypeError TypedPPM
```
([PPM/Check.lean](PPM/Check.lean))

```lean
def checkPPMProgram (Γ : TypedEnv) (caps : List Capability) (s : Stmt) :
    Except TypeError PPMState
```
([PPMProgram/Check.lean](PPMProgram/Check.lean))

## Example

The judgment's input data, in the binary-symplectic syntax it consumes
([Transversal/Examples.lean](Transversal/Examples.lean)):

```lean
-- the single-qubit Hadamard as a 2×2 symplectic (X↔Z):
hGate : BoolMat := [[false, true], [true, false]]

-- a single logical qubit, no stabilizers (X̄ = X, Z̄ = Z):
oneQ : Block := { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }

-- the complete [[3,1,1]] repetition code (Z₀Z₁, Z₁Z₂; X̄ = XXX, Z̄ = Z₀):
rep3 : Block :=
  { n := 3,
    stab := [[false, false, false, true,  true,  false],
             [false, false, false, false, true,  true ]],
    lx := [[true,  true,  true,  false, false, false]],
    lz := [[false, false, false, true,  false, false]] }
```

`checkTransversal Γ b g` succeeds only if the tensor-power of the single-qubit gate `g`
is symplectic and preserves the block's stabilizers. Feeding the values above:

```lean
-- transversal H on oneQ: the tensor power is the symplectic J 1 ( = [[F,T],[T,F]] ),
-- which preserves the (empty) stabilizer and induces X̄ ↦ Z̄:
hGate on oneQ   -- OK: induced logical action inducedLX = [[false, true]]  (X̄ ↦ Z̄)

-- transversal H on the non-self-dual repetition code:
hGate on rep3   -- rejected: J 3 does not preserve the rep-code stabilizers (Z₀Z₁, Z₁Z₂)
```

Source: [Transversal/Examples.lean](Transversal/Examples.lean).

## Status & scope

These judgments are **static** — they decide representational legality and emit typed
certificates; runtime semantics live in `PPM` and `Compiler/Mixed`. Honest tiers
(per [Compiler/CONTRACT.md](../../Compiler/CONTRACT.md)):

- **D (`by decide`)** — the acceptance/rejection behaviour of each checker is pinned by
  worked examples in the `Examples.lean` of each subfolder (e.g. transversal H legal on
  self-dual codes, rejected on the repetition code; inter-block CNOT incidence checks).
- **P (proved theorem)** — [PPMProgram/Soundness.lean](PPMProgram/Soundness.lean) carries
  the structural soundness theorems for whole PPM statements: `checkPPMStmt_meas_sound`,
  `checkPPMStmt_targets_valid`, `checkPPMStmt_dead_mono`, and
  `checkPPMStmt_no_use_after_discard` (no use-after-discard).
- **A / M (assumed / planned)** — these are *legality* judgments over the
  binary-symplectic / GF(2) representation. They do **not** establish channel
  correctness, fault tolerance, code distance, decoder behaviour, or operational
  equivalence of the resulting physical circuits; those obligations are explicitly
  **deferred** to downstream layers and are not discharged here. Judgments consume a
  well-formed `TypedEnv`, so malformed blocks are unrepresentable at the judgment level;
  boundary `*FromEnv` functions validate raw `Env` values before delegating.

## See also

- [../README.md](../README.md) — the TypeChecker overview (parent).
- [Transversal/README.md](Transversal/README.md) — local gates and automorphisms.
- [Switch/README.md](Switch/README.md) — code switching.
- [PPM/README.md](PPM/README.md) — logical Pauli measurement capability matching.
- [PPMProgram/README.md](PPMProgram/README.md) — whole PPM statement checking.
