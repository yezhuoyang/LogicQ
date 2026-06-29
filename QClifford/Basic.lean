/-
  QClifford — umbrella for the final target IR (level L_QClifford).

  A circuit of physical Clifford gates, `Z`-basis measurements, and
  classically-conditioned Pauli corrections; `QClifford.run` executes it against
  a parametric physical host, with `run_append` as the composition law.
-/
import QClifford.Syntax
import QClifford.Semantics
import QClifford.Parse
