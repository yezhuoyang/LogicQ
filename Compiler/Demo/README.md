# Compiler/Demo

> Worked end-to-end examples that keep the compiler honest about its correctness boundaries.

This folder holds small, `by decide`-checked demo programs that exercise the full LogicQ
pipeline — ChainQ source `LogicalOp` programs and family codes -> `compile?` (source-check +
lower) -> Mixed IR `checkLogicalExec` (TypeChecker legality) -> the `execMixed` operational
interpreter / `runGates` ideal simulator. Each example is explicitly labelled with WHERE its
guarantee stops (exact-operational, ideal-channel-assumed, typechecked-only, or deferred), so
no demo can be read as claiming more than is actually proved.

## What's here

| Module | Role |
|---|---|
| [Common.lean](Common.lean) | Shared fixtures: `demoCfg`, `dj2Cfg`, `famCfg`, `envN`, `tenv2`, `tenv4`. |
| [Direct.lean](Direct.lean) | §1 direct fragment — full pipeline, exact source = emitted for `H ; S ; H`. |
| [Algorithms.lean](Algorithms.lean) | §2–§4 textbook DJ/Grover/Simon as `LogicalOp` programs, ideal outcomes, well-formed-vs-compilable split. |
| [Frames.lean](Frames.lean) | §5 real operational semantics (`execMixed`), §5b exact-operational fragment classifier, §6 negative well-formedness. |
| [Entangling.lean](Entangling.lean) | §7 typechecked CNOT lowering to a PPM gadget — a real compiler path, NOT a channel-correctness claim. |
| [Families.lean](Families.lean) | §8 real ChainQ family codes (surface/toric/HGP/BB/lifted-product) through `cssToTypedBlock?` + `compile?`. |
| [Contract.lean](Contract.lean) | M22 contract examples: the three end-to-end fragments at their explicit `opBoundary` boundaries. |

## Key definitions

```lean
/-- `true` iff the op has EXACT operational semantics: logical Paulis
    (`xGate`/`zGate` → APPLIED `.pauli`) and direct Cliffords ... -/
def exactSupportedOp : LogicalOp → Bool
  | .hGate _ | .sGate _ | .xGate _ | .zGate _ | .blockTransversal _ _ => true
  | .transversalLogicalCNOT _ _ _ => true
  | .transversalLogicalCNOTBatch _ _ _ _ => true
  | _ => false
```
(from [Frames.lean](Frames.lean))

```lean
/-- The demo compile configuration (no capabilities, ancilla seed in block 1). -/
def demoCfg : CompileConfig := { caps := [], anc := ⟨1, 0⟩ }

/-- An `n`-block env: `n` bare single-logical qubits (blocks `0..n-1`). -/
def envN : Nat → TypedEnv
  | 0     => ⟨[]⟩
  | n + 1 => ⟨⟨q0, by decide⟩ :: (envN n).blocks⟩
```
(from [Common.lean](Common.lean))

```lean
/-- Build a single-block `TypedEnv` from a checked CSS family code ... -/
def envOf : Except ChainQError CheckedCSSCode → TypedEnv
  | .ok cc => match cssToTypedBlock? cc with | .ok tb => ⟨[tb]⟩ | .error _ => ⟨[]⟩
  | .error _ => ⟨[]⟩
```
(from [Families.lean](Families.lean))

## Example

```lean
def hsSrc : List LogicalOp := [.hGate ⟨0, 0⟩, .sGate ⟨0, 0⟩]

example : (match compile? .executable demoCfg tenvQ hsSrc with
           | .ok c => decide (execMixed (Layout.flat 4) 1 c.prog (init 1)
                              = some (runGates 1 (sourceGates (Layout.flat 4) hsSrc) (init 1)))
           | .error _ => false) = true := by decide
example : hsSrc.all (fun op => opBoundary op == GadgetBoundary.exact) = true := by decide
```

`H ; S` lowers to direct transversals; running the EMITTED program through the operational
interpreter `execMixed` yields the SAME state as the ideal source circuit `runGates`, and every
op sits at the `GadgetBoundary.exact` boundary. This is the strongest demo guarantee — exact
operational equality, not an assumption. Source: [Contract.lean](Contract.lean) (§1).

## Status & scope

Every claim in this folder is a `by decide` test (tier **D** in [../CONTRACT.md](../CONTRACT.md)),
not a general theorem — the demos pin concrete fixtures, they do not quantify over all programs.
Within that, the demos are careful about boundaries:

- **Exact-operational (run, matched)**: logical Paulis (`xGate`/`zGate`), direct Cliffords
  (`hGate`/`sGate` on `k=1` blocks, `blockTransversal` H/S) — `execMixed` actually runs them and
  the result equals the ideal `runGates` simulator (`Frames.lean` §5, `Contract.lean` §1).
- **Ideal-channel ASSUMED (typechecked, not run)**: `cnotGate` lowers to a real multi-`.meas`
  PPM gadget that type-checks given adapter capabilities, but `execMixed` is `none`/stuck on the
  gadget — `opBoundary (.cnotGate …) = .idealChannel`; channel correctness is the deferred
  ideal-gadget assumption (tier **A**), NOT proved. `czGate` rides a PLACEHOLDER `progCZAt` and
  is flagged EXPERIMENTAL.
- **Typechecked-only / deferred**: `tGate` is a deferred magic obligation
  (`opBoundary (.tGate …) = .typecheckedOnly`); `measure` is an ideal projective readout. The
  code-switch demo (`Contract.lean` §3) typechecks against the PROVED symplectic `checkSwitch`
  certificate, but distance/decoder/fault-tolerance remain deferred obligations.

Honesty is enforced operationally: `execMixed` returns `none` (stuck) on instructions it cannot
run rather than silently dropping them (`Frames.lean` §5), so a gadget demo cannot masquerade as
an operational-correctness result.

## See also

- [../README.md](../README.md) — the Compiler stack overview.
- [../CONTRACT.md](../CONTRACT.md) — the P/D/A/M correctness-tier contract these demos are pinned to.

(No child directories: every module in this folder is a single `.lean` file.)
