# ChainQ/Checked

Validity-carrying public constructors.

## Syntax

```lean
structure CheckedCSSCode where
  code  : CSSCode
  valid : code.valid = true
```

Family constructors return `Except ChainQError CheckedCSSCode`.

## Typechecking Rule

`mkCSS` packages a code only after `CSSCode.valid`.  `mkLogicalBasis` derives a
basis and returns it only if `CSSLogicalBasis.valid` succeeds.

## Semantics

Checked values are the safe boundary into the typechecker elaborator.  A
malformed code cannot be passed as a `CheckedCSSCode`.

## Example

```lean
ChainQ.mkSurface 2
ChainQ.mkLogicalBasis checkedCode
```
