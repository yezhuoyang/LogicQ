/-
  QStab — umbrella for the physical stabilizer-measurement IR (level L_QStab).

  A dataflow of physical Pauli measurements (`Prop[r,s] P`) and classical
  parities (`Parity c…`); `QStab.eval` computes the syndrome / logical-readout
  bits from the measurement outcomes.
-/
import QStab.Syntax
import QStab.Semantics
