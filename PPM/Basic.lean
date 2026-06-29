/-
  PPM — umbrella for the QMeas measurement-based language (level L_PPM).

  Syntax: Pauli measurements, the adaptive `if r = +1 then … else …`
  conditional, bounded loops, Pauli-frame updates, `discard`, `abort`.
  Semantics: a small-step operational semantics with `abort` as a stuck
  terminal; the Hadamard gadget's frame table is derived from the rules
  (`PPM.progH_frame`).
-/
import PPM.Syntax
import PPM.Semantics
import PPM.Parse
