# TypeChecker/Judgment/Switch

Typed code switching.

## Syntax

```lean
structure SwitchCert where
  kind : SwitchKind
  f    : BoolMat

checkSwitch Gamma b target cert
```

`f` maps symplectic rows of the source code to rows of the target code.

## Typechecking Rule

The checker requires:

- source block exists, is live, and is owned
- target block is valid
- `f` has shape `2*n_source x 2*n_target`
- source stabilizers map into the target stabilizer span
- logical X and Z bases agree modulo target stabilizers

## Semantics

Success replaces the source block with the target block in the typed
environment and records protocol obligations.

## Example

The bare-qubit-to-repetition-code example maps `Xbar` to `XXX` and `Zbar` to
`Z0`; malformed maps are rejected.
