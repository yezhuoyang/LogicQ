# ChainQ/HGPCode

Hypergraph-product codes and their repetition-code inputs.

## Syntax

```lean
repOpen d
repCyc d
Internal.hgp h1 h2 m1 n1 m2 n2
hgp? h1 h2 m1 n1 m2 n2
mkHGP h1 h2 m1 n1 m2 n2
```

## Semantics

The raw HGP constructor builds:

```text
hx = [h1 kron I_n2 | I_m1 kron h2^T]
hz = [I_n1 kron h2 | h1^T kron I_m2]
n  = n1*n2 + m1*m2
```

## Typechecking Rule

The checked variants require the declared matrix shapes to match the actual
inputs and require all dimensions to be positive.  `mkHGP` additionally packages
the CSS-validity proof.

## Example

`surface d` is defined as `HGP(repOpen d, repOpen d)`.
