# LogicQ

> The full public umbrella: `import LogicQ.Basic` pulls in every implemented layer of the stack.

`LogicQ` is the top-level aggregate of the LogicQ verified-compilation pipeline (a
&ldquo;quantum CompCert&rdquo;). It owns no language of its own — it is a single re-export
module so a demo or paper experiment can pull in the whole stack with one import. Under the
root-clean layout, every top-level folder owns exactly one public aggregate
`<Folder>/Basic.lean`, and this folder's [Basic.lean](Basic.lean) imports all of them.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | The full-pipeline umbrella; re-exports the public entrypoint of every implemented layer. |

## Key definitions

This module defines nothing of its own; it is exactly the following import list
([Basic.lean](Basic.lean)):

```lean
import Logical.Basic
import Physical.Basic
import ChainQ.Basic
import PPR.Basic
import PPM.Basic
import QStab.Basic
import QClifford.Basic
import TypeChecker.Basic
import Compiler.Basic
```

(The magic-state layer [MagicQ](../MagicQ/README.md) is a separate aggregate — import
`MagicQ.Basic` directly when you need it.)

## Example

```lean
-- pull in the whole stack:
import LogicQ.Basic
```

Use this when you need the entire pipeline at once; use a more precise `*.Basic` import (e.g.
`import ChainQ.Basic`) when reviewing a single layer.

## Status & scope

Pure aggregator — no syntax, no semantics, no theorems of its own. The honest proved-vs-deferred
status of each layer it re-exports lives in that layer's own README and in
[Compiler/CONTRACT.md](../Compiler/CONTRACT.md). Root-level `.lean` files are intentionally
forbidden (M21 root-clean layout); this README documents the umbrella, not a language.

## See also

- Parent: [../README.md](../README.md) — repository root and full stack overview.
- The layers re-exported here: [Logical](../Logical/README.md), [Physical](../Physical/README.md),
  [ChainQ](../ChainQ/README.md), [PPR](../PPR/README.md), [PPM](../PPM/README.md),
  [QStab](../QStab/README.md), [QClifford](../QClifford/README.md),
  [TypeChecker](../TypeChecker/README.md), [Compiler](../Compiler/README.md).
