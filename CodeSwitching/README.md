# CodeSwitching

> Reserved source-level layer for code-switching protocols — currently a stub with no Lean modules.

This folder is a placeholder reserved for *source-level* code-switching program syntax: switching a live logical block from one code family to another, including success branches and Pauli byproduct rules. It sits at the front of the LogicQ stack (alongside ChainQ code families), upstream of the TypeChecker legality judgments and the Compiler Mixed IR that eventually lower to the QStab/QClifford physical target. As of this writing the layer contains **only this README** — the actual code-switching logic lives in sibling folders (see below).

## What's here

This folder currently has **no `.lean` modules** and no child directories — only this `README.md`. The work that would belong here is, for now, implemented elsewhere in the repository.

| Module | Role |
| ------ | ---- |
| _(none yet)_ | Source-level switch syntax is planned but not implemented in this folder. |

## Key definitions

There are no Lean definitions in this folder. The static and certificate-level pieces of code switching that *do* exist live in sibling layers:

- Static switch legality is implemented in [`TypeChecker/Judgment/Switch`](../TypeChecker/Judgment/Switch/README.md) (`Cert.lean`, `Check.lean`, `Examples.lean`).
- External protocol certificate records live in [`Compiler/CodeSwitch`](../Compiler/CodeSwitch/README.md) (`Basic.lean`, `DimensionJump.lean`, `ProductSurgery.lean`, `GPPMSemantics.lean`, and others).

## Example

This folder has only a stub README, so there is no Lean example to quote from it. The full current contents of `CodeSwitching/README.md` (prior to this rewrite) were:

```markdown
# CodeSwitching

Reserved for source-level code-switching protocols.

## Intended Syntax

This folder should eventually contain program syntax for switching a live
logical block from one code family to another, including success branches and
byproduct rules.

## Current Status

Static switch legality is implemented in `TypeChecker/Judgment/Switch`.
External protocol certificate records live in `Compiler/CodeSwitch`.
```

Cited from [README.md](README.md) (this file, pre-rewrite).

## Status & scope

**Stub / planned (M in the Compiler/CONTRACT.md tiering).** Nothing is proved or wired in this folder because it contains no code. Per the contract's honest-scope tiers, everything intended for this layer is currently **M (missing/planned)**:

- The source-level switch syntax (code-family transition with success branches and byproduct rules) is **planned**, not implemented.
- No theorems (P), `by decide` tests (D), or documented assumptions (A) exist here.

What *is* implemented elsewhere keeps its own scope: the [`TypeChecker/Judgment/Switch`](../TypeChecker/Judgment/Switch/README.md) judgments cover *static* switch legality only, and the [`Compiler/CodeSwitch`](../Compiler/CodeSwitch/README.md) records are **external protocol certificates** (documented assumptions / external references) — channel-correctness, fault-tolerance, distance, and operational-equivalence claims for code switching remain **deferred**. Do not read this folder as evidence that code switching is end-to-end verified.

## See also

- [../README.md](../README.md) — LogicQ repository root README.
- [../TypeChecker/Judgment/Switch/README.md](../TypeChecker/Judgment/Switch/README.md) — static switch-legality judgments (where the real type-level check lives).
- [../Compiler/CodeSwitch/README.md](../Compiler/CodeSwitch/README.md) — external code-switch protocol certificate records.
