# LogicQ

The full public umbrella.

## Syntax

There is no separate surface syntax here.  `LogicQ.Basic` imports the public
entrypoints of every implemented layer:

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

## Rule

Use this import when a demo or paper experiment needs the whole stack.  Use a
more precise `*.Basic` import when reviewing one layer.

## Example

```lean
import LogicQ.Basic
```
