# TypeChecker/Judgment/Transversal

Legal transversal gates and logical automorphisms.

## Syntax

```lean
checkLogicalAutomorphism Gamma b M
checkTransversal Gamma b g
```

`M` is a `2n x 2n` symplectic matrix.  `g` is a local `2 x 2` single-qubit
symplectic matrix whose tensor power is built internally.

## Typechecking Rule

The checker requires:

- block `b` exists and is live
- matrix shape is correct
- the map preserves the symplectic form
- stabilizers map back into the stabilizer span

## Semantics

Success returns the induced action on the declared logical X/Z basis.

## Example

Transversal H on a bare qubit succeeds; transversal H on the repetition example
is rejected when it fails to preserve stabilizers.
