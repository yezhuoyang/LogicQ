/-
  PPR — umbrella for the Pauli-Product-Rotation IR (level L_PPR).

  A PPR program is a sequence of logical Pauli-product rotations `exp(i φ P)`,
  with `φ ∈ ±{π, π/2, π/4, π/8}` over the logical qubits in `P`'s support.
  PPR sits above PPM and lowers into it; the `π/8` count is the T-count.
-/
import PPR.Syntax
import PPR.Semantics
