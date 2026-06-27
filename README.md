# LogicQ

LogicQ is a Lean 4 workspace for a verified QEC compilation stack.  The code is
organized as small languages, each with its own syntax, semantics, and checker.

The current wired compiler path is:

```text
ChainQ code families -> TypeChecker.TypedEnv -> Compiler LogicalOp -> Mixed IR
```

The longer target stack is:

```text
ChainQ -> PPR -> PPM -> surgery/adapter -> QStab -> QClifford
```

Some of those languages are implemented as standalone specs before the lowering
passes between them are built.  The honest contract is in
[Compiler/CONTRACT.md](Compiler/CONTRACT.md).

## Public Imports

The repository root intentionally has no `.lean` files.  Import public layers
through their folder-owned entrypoints:

```lean
import LogicQ.Basic
import ChainQ.Basic
import TypeChecker.Basic
import Compiler.Basic
import PPM.Basic
```

Each source folder has its own README with the local syntax, semantic rule, and
small examples.

## Folders

| Folder | What lives there |
|---|---|
| [Logical](Logical/README.md) | logical block and logical-qubit addresses |
| [Physical](Physical/README.md) | physical qubits and physical Pauli strings |
| [ChainQ](ChainQ/README.md) | chain-complex/CSS code type system and code families |
| [TypeChecker](TypeChecker/README.md) | legality checks for logical operations |
| [Compiler](Compiler/README.md) | source LogicalOp -> Mixed IR compiler and demos |
| [PPR](PPR/README.md) | Pauli-product rotations |
| [PPM](PPM/README.md) | adaptive Pauli-product measurement programs |
| [QStab](QStab/README.md) | physical stabilizer-measurement dataflow |
| [QClifford](QClifford/README.md) | physical Clifford target circuit |
| [MagicQ](MagicQ/README.md) | planned magic-state protocol language |
| [LatticeSurgery](LatticeSurgery/README.md) | planned surgery/adapter language |
| [Library](Library/README.md) | source-only arXiv library and notes |

## Build

```powershell
lake build
lake build LogicQ.Basic ChainQ.Basic TypeChecker.Basic Compiler.Basic
```

The project uses Lean 4.29.1 and Mathlib 4.29.1.  Most of the stack is
Mathlib-free; the PPR denotation uses Mathlib matrices and complex numbers.
