# MagicQ

Reserved for the magic-state protocol language.

## Intended Syntax

MagicQ should describe factories, cultivation, injection, postselection, and
success/failure branches:

```text
protocol name(args):
  repeat body until success
  return resource
```

## Intended Typechecking Rule

The checker should track consumed magic resources, prepared bases, measurement
outcomes, postselection predicates, and classical frame updates.

## Current Status

No Lean implementation lives here yet.  The current compiler represents `T` as a
typed `MagicObligation` in `Compiler/Mixed/Syntax`; it typechecks but has no
runtime `Step`.
