/-
  Compiler.QASM.Benchmarks - curated QASMBench end-to-end regression suite.

  Sources are copied from pnnl/QASMBench at commit
  357b942396d5c2b7cbc1c229c585a6ef5ccaebac.  The positive suite intentionally
  uses only benchmark programs whose raw OpenQASM vocabulary is inside the current
  LogicQ QASM contract.  The blocked suite records representative scientific
  benchmarks that remain outside the exact language contract.
-/
import Compiler.QASM.Physical

set_option maxRecDepth 200000

namespace Compiler.QASM.Benchmarks

open Compiler.QASM Compiler.ChainQ2Mixed TypeChecker

/-- One embedded QASMBench source plus the resource counts needed by the packed-box setup. -/
structure BenchCase where
  name       : String
  category   : String
  sourcePath : String
  qubits     : Nat
  hCount     : Nat
  plusCount  : Nat
  qasm       : String

/-- A QASMBench source that is intentionally outside the current exact QASM contract. -/
structure BlockedCase where
  name       : String
  category   : String
  sourcePath : String
  blocker    : String

def logicalName (pref : String) (i : Nat) : String := pref ++ toString i

/-- Logical-box variant A: one one-logical bare ChainQ block per QASM virtual qubit. -/
def separatedBareDecl (i : Nat) : ChainQ.NamedCodeDecl :=
  { ChainQ.indexedBareDecl with name := logicalName "q" i }

def separatedBareData (i : Nat) : NamedLogical :=
  { code := logicalName "q" i, logical := "data" }

def separatedBareRequest (n : Nat) : AllocationRequest :=
  { decls := (List.range n).map separatedBareDecl,
    dataLogicals := (List.range n).map separatedBareData,
    ancillas := [],
    cnotMode := .strictTransversal,
    cnotIncidence := some [[true]] }

/-- Logical-box variant B: one packed bare block with data plus sized |0>/|+> pools. -/
def packedNames (q zeroCount plusCount : Nat) : List String :=
  (List.range q).map (logicalName "d") ++
  (List.range zeroCount).map (logicalName "z") ++
  (List.range plusCount).map (logicalName "p")

def packedBareDecl (q zeroCount plusCount : Nat) : ChainQ.NamedCodeDecl :=
  { name := "box",
    decl := .css { n := q + zeroCount + plusCount, hx := [], hz := [] },
    logicalIndex := some
      { names := packedNames q zeroCount plusCount,
        pauliBasis :=
          { zBasis := idMat (q + zeroCount + plusCount),
            xDualBasis := idMat (q + zeroCount + plusCount) } } }

def packedData (i : Nat) : NamedLogical :=
  { code := "box", logical := logicalName "d" i }

def packedZeroAncilla (i : Nat) : NamedAnc :=
  { code := "box", logical := logicalName "z" i, basis := .zero }

def packedPlusAncilla (i : Nat) : NamedAnc :=
  { code := "box", logical := logicalName "p" i, basis := .plus }

def packedBareRequest (q zeroCount plusCount : Nat) : AllocationRequest :=
  { decls := [packedBareDecl q zeroCount plusCount],
    dataLogicals := (List.range q).map packedData,
    ancillas :=
      (List.range zeroCount).map packedZeroAncilla ++
      (List.range plusCount).map packedPlusAncilla,
    cnotMode := .ppmOnly }

def compilesWithSeparatedBare (b : BenchCase) : Bool :=
  ok? (compileOpenQASM2ToMixIR? [] b.qasm (separatedBareRequest b.qubits))

def compilesWithPackedBare (b : BenchCase) : Bool :=
  ok? (compileOpenQASM2ToMixIR? [] b.qasm
    (packedBareRequest b.qubits b.hCount b.plusCount))

def compilesPhysicallyWithSeparatedBare (b : BenchCase) : Bool :=
  ok? (compileOpenQASM2ToQClifford? [] b.qasm (separatedBareRequest b.qubits))

def tMagicBench (b : BenchCase) : Bool :=
  b.name == "teleportation_n3" || b.name == "qec_en_n5"

/-- The positive QASMBench suite: raw QASM sources that compile end-to-end today. -/
def positiveSuite : List BenchCase := [
  { name := "qrng_n4", category := "QRNG", sourcePath := "small/qrng_n4/qrng_n4.qasm",
    qubits := 4, hCount := 4, plusCount := 0, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg q[4];
creg c[4];

h q[0];
h q[1];
h q[2];
h q[3];

measure q[0] -> c[0];
measure q[1] -> c[1];
measure q[2] -> c[2];
measure q[3] -> c[3];
" },
  { name := "deutsch_n2", category := "Deutsch", sourcePath := "small/deutsch_n2/deutsch_n2.qasm",
    qubits := 2, hCount := 3, plusCount := 1, qasm := "// Implementation of Deutsch algorithm with two qubits for f(x)=x
OPENQASM 2.0;
include \"qelib1.inc\";

qreg q[2];
creg c[2];

x q[1];
h q[0];
h q[1];
cx q[0],q[1];
h q[0];
measure q[0] -> c[0];
measure q[1] -> c[1];
" },
  { name := "iswap_n2", category := "iSWAP", sourcePath := "small/iswap_n2/iswap_n2.qasm",
    qubits := 2, hCount := 4, plusCount := 4, qasm := "// Name of Experiment: iswap v4

OPENQASM 2.0;
include \"qelib1.inc\";

qreg q[2];
creg c[2];

x q[0];
s q[0];
s q[1];
h q[0];
cx q[0],q[1];
h q[0];
h q[1];
cx q[0],q[1];
h q[0];
measure q[0] -> c[0];
measure q[1] -> c[1];
" },
  { name := "cat_state_n4", category := "Cat/GHZ", sourcePath := "small/cat_state_n4/cat_state_n4.qasm",
    qubits := 4, hCount := 1, plusCount := 3, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg bits[4];
creg c[4];

h bits[0];
cx bits[0],bits[1];
cx bits[1],bits[2];
cx bits[2],bits[3];

measure bits[0] -> c[0];
measure bits[1] -> c[1];
measure bits[2] -> c[2];
measure bits[3] -> c[3];
" },
  { name := "grover_n2", category := "Grover", sourcePath := "small/grover_n2/grover_n2.qasm",
    qubits := 2, hCount := 10, plusCount := 2, qasm := "// Name of Experiment: Grover N=2 A=10 v1

OPENQASM 2.0;
include \"qelib1.inc\";


qreg q[2];
creg c[2];

h q[0];
h q[1];

h q[1];
cx q[0],q[1];
h q[1];

h q[0];
h q[1];
x q[0];
x q[1];
h q[1];
cx q[0],q[1];
h q[1];
x q[0];
x q[1];

h q[0];
h q[1];
measure q[0] -> c[0];
measure q[1] -> c[1];
" },
  { name := "lpn_n5", category := "LPN", sourcePath := "small/lpn_n5/lpn_n5.qasm",
    qubits := 5, hCount := 9, plusCount := 2, qasm := "// Name of Experiment: LPN circuit 2 v1

OPENQASM 2.0;
include \"qelib1.inc\";

qreg q[5];
creg c[5];

h q[0];
h q[1];
h q[3];
h q[4];
cx q[3], q[2];
cx q[0], q[2];
h q[0];
h q[1];
h q[2];
h q[3];
h q[4];
measure q[0] -> c[0];
measure q[1] -> c[1];
measure q[2] -> c[2];
measure q[3] -> c[3];
measure q[4] -> c[4];
" },
  { name := "teleportation_n3", category := "Teleportation", sourcePath := "small/teleportation_n3/teleportation_n3.qasm",
    qubits := 3, hCount := 4, plusCount := 3, qasm := "// Teleportation using 3 qubits.
// Description: Based on the example given by S. Fedortchenko (https://arxiv.org/pdf/1607.02398.pdf) 

OPENQASM 2.0;
include \"qelib1.inc\";

qreg q[3];
creg c[3];

h q[0];
t q[0];
h q[0];
h q[2];
s q[0];
cx q[2],q[1];
cx q[0],q[1];
h q[0];
measure q[0] -> c[0];
measure q[1] -> c[1];
measure q[2] -> c[2];
" },
  { name := "hs4_n4", category := "Hidden shift", sourcePath := "small/hs4_n4/hs4_n4.qasm",
    qubits := 4, hCount := 20, plusCount := 4, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg q[4];
creg c[4];
h q[0];
h q[1];
h q[2];
h q[3];
x q[0];
x q[2];
h q[1];
h q[3];
cx q[0],q[1];
cx q[2],q[3];
h q[1];
h q[3];
x q[0];
x q[2];
h q[0];
h q[1];
h q[2];
h q[3];
h q[1];
h q[3];
cx q[0],q[1];
cx q[2],q[3];
h q[1];
h q[3];
h q[0];
h q[1];
h q[2];
h q[3];
measure q[0] -> c[0];
measure q[1] -> c[1];
measure q[2] -> c[2];
measure q[3] -> c[3];
" },
  { name := "qec_en_n5", category := "QEC", sourcePath := "small/qec_en_n5/qec_en_n5.qasm",
    qubits := 5, hCount := 14, plusCount := 10, qasm := "// Name of Experiment: Encoder into bit-flip code with parity checks (qubits 0,1,3) v2

OPENQASM 2.0;
include \"qelib1.inc\";

qreg q[5];
creg c[5];

h q[2];
t q[2];
h q[2];
h q[0];
h q[1];
h q[2];
cx q[1], q[2];
cx q[0], q[2];
h q[0];
h q[1];
h q[3];
cx q[3], q[2];
h q[2];
h q[3];
cx q[3], q[2];
cx q[0], q[2];
cx q[1], q[2];
h q[2];
h q[4];
cx q[4], q[2];
h q[2];
h q[4];
cx q[4], q[2];
cx q[1], q[2];
cx q[3], q[2];


measure q[2] -> c[2];
measure q[4] -> c[4];
measure q[0] -> c[0];
measure q[1] -> c[1];
measure q[3] -> c[3];
" },
  { name := "bb84_n8", category := "BB84", sourcePath := "small/bb84_n8/bb84_n8.qasm",
    qubits := 8, hCount := 18, plusCount := 0, qasm := "// Generated from Cirq v0.8.0

OPENQASM 2.0;
include \"qelib1.inc\";


// Qubits: [0, 1, 2, 3, 4, 5, 6, 7]
qreg q[8];

creg m6[1];
creg m0[1];
creg m3[1];
creg m1[1];
creg m2[1];
creg m4[1];
creg m5[1];
creg m7[1];


x q[0];
h q[1];
x q[2];
x q[3];
x q[4];
x q[5];
h q[7];
measure q[6] -> m6[0];
h q[5];
h q[1];
h q[2];
h q[4];
h q[7];
measure q[0] -> m0[0];
measure q[3] -> m3[0];
measure q[1] -> m1[0];
measure q[2] -> m2[0];
measure q[4] -> m4[0];
measure q[5] -> m5[0];
measure q[7] -> m7[0];
x q[0];
h q[1];
x q[2];
x q[3];
x q[4];
h q[7];
h q[5];
h q[6];
h q[2];
h q[4];
h q[1];
h q[3];
h q[7];
measure q[0] -> m0[0];
measure q[5] -> m5[0];
measure q[6] -> m6[0];
h q[2];
h q[4];
measure q[1] -> m1[0];
measure q[3] -> m3[0];
measure q[7] -> m7[0];
measure q[2] -> m2[0];
measure q[4] -> m4[0];
" },
  { name := "qec9xz_n17", category := "QEC", sourcePath := "medium/qec9xz_n17/qec9xz_n17.qasm",
    qubits := 17, hCount := 21, plusCount := 32, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg q0[9];
qreg q1[8];
creg c0[8];
h q0[0];
cx q0[0],q0[3];
cx q0[0],q0[6];
h q0[0];
h q0[3];
h q0[6];
cx q0[0],q0[1];
cx q0[0],q0[2];
cx q0[3],q0[4];
cx q0[3],q0[5];
cx q0[6],q0[7];
cx q0[6],q0[8];
cx q0[0],q1[0];
cx q0[1],q1[0];
cx q0[1],q1[1];
cx q0[2],q1[1];
cx q0[3],q1[2];
cx q0[4],q1[2];
cx q0[4],q1[3];
cx q0[5],q1[3];
cx q0[6],q1[4];
cx q0[7],q1[4];
cx q0[7],q1[5];
cx q0[8],q1[5];
measure q1[0] -> c0[0];
measure q1[1] -> c0[1];
measure q1[2] -> c0[2];
measure q1[3] -> c0[3];
measure q1[4] -> c0[4];
measure q1[5] -> c0[5];
h q0[0];
h q0[1];
h q0[2];
h q0[3];
h q0[4];
h q0[5];
h q0[6];
h q0[7];
h q0[8];
cx q0[0],q1[6];
cx q0[3],q1[7];
cx q0[1],q1[6];
cx q0[4],q1[7];
cx q0[2],q1[6];
cx q0[5],q1[7];
cx q0[3],q1[6];
cx q0[6],q1[7];
cx q0[4],q1[6];
cx q0[7],q1[7];
cx q0[5],q1[6];
cx q0[8],q1[7];
measure q1[6] -> c0[6];
measure q1[7] -> c0[7];
h q0[0];
h q0[1];
h q0[2];
h q0[3];
h q0[4];
h q0[5];
h q0[6];
h q0[7];
" },
  { name := "cat_state_n22", category := "Cat/GHZ", sourcePath := "medium/cat_state_n22/cat_state_n22.qasm",
    qubits := 22, hCount := 1, plusCount := 21, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg q[22];
creg c[22];
creg meas[22];
h q[0];
cx q[0],q[1];
cx q[1],q[2];
cx q[2],q[3];
cx q[3],q[4];
cx q[4],q[5];
cx q[5],q[6];
cx q[6],q[7];
cx q[7],q[8];
cx q[8],q[9];
cx q[9],q[10];
cx q[10],q[11];
cx q[11],q[12];
cx q[12],q[13];
cx q[13],q[14];
cx q[14],q[15];
cx q[15],q[16];
cx q[16],q[17];
cx q[17],q[18];
cx q[18],q[19];
cx q[19],q[20];
cx q[20],q[21];
barrier q[0],q[1],q[2],q[3],q[4],q[5],q[6],q[7],q[8],q[9],q[10],q[11],q[12],q[13],q[14],q[15],q[16],q[17],q[18],q[19],q[20],q[21];
measure q[0] -> meas[0];
measure q[1] -> meas[1];
measure q[2] -> meas[2];
measure q[3] -> meas[3];
measure q[4] -> meas[4];
measure q[5] -> meas[5];
measure q[6] -> meas[6];
measure q[7] -> meas[7];
measure q[8] -> meas[8];
measure q[9] -> meas[9];
measure q[10] -> meas[10];
measure q[11] -> meas[11];
measure q[12] -> meas[12];
measure q[13] -> meas[13];
measure q[14] -> meas[14];
measure q[15] -> meas[15];
measure q[16] -> meas[16];
measure q[17] -> meas[17];
measure q[18] -> meas[18];
measure q[19] -> meas[19];
measure q[20] -> meas[20];
measure q[21] -> meas[21];
" },
  { name := "ghz_state_n23", category := "Cat/GHZ", sourcePath := "medium/ghz_state_n23/ghz_state_n23.qasm",
    qubits := 23, hCount := 1, plusCount := 22, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg q[23];
creg c[23];
creg meas[23];
h q[0];
cx q[0],q[1];
cx q[1],q[2];
cx q[2],q[3];
cx q[3],q[4];
cx q[4],q[5];
cx q[5],q[6];
cx q[6],q[7];
cx q[7],q[8];
cx q[8],q[9];
cx q[9],q[10];
cx q[10],q[11];
cx q[11],q[12];
cx q[12],q[13];
cx q[13],q[14];
cx q[14],q[15];
cx q[15],q[16];
cx q[16],q[17];
cx q[17],q[18];
cx q[18],q[19];
cx q[19],q[20];
cx q[20],q[21];
cx q[21],q[22];
barrier q[0],q[1],q[2],q[3],q[4],q[5],q[6],q[7],q[8],q[9],q[10],q[11],q[12],q[13],q[14],q[15],q[16],q[17],q[18],q[19],q[20],q[21],q[22];
measure q[0] -> meas[0];
measure q[1] -> meas[1];
measure q[2] -> meas[2];
measure q[3] -> meas[3];
measure q[4] -> meas[4];
measure q[5] -> meas[5];
measure q[6] -> meas[6];
measure q[7] -> meas[7];
measure q[8] -> meas[8];
measure q[9] -> meas[9];
measure q[10] -> meas[10];
measure q[11] -> meas[11];
measure q[12] -> meas[12];
measure q[13] -> meas[13];
measure q[14] -> meas[14];
measure q[15] -> meas[15];
measure q[16] -> meas[16];
measure q[17] -> meas[17];
measure q[18] -> meas[18];
measure q[19] -> meas[19];
measure q[20] -> meas[20];
measure q[21] -> meas[21];
measure q[22] -> meas[22];
" },
  { name := "bv_n14", category := "Bernstein-Vazirani", sourcePath := "medium/bv_n14/bv_n14.qasm",
    qubits := 14, hCount := 27, plusCount := 13, qasm := "//@author Raymond Harry Rudy rudyhar@jp.ibm.com
//Bernstein-Vazirani with 14 qubits.
//Hidden string is 1111111111111
OPENQASM 2.0;
include \"qelib1.inc\";
qreg qr[14];
creg cr[13];
h qr[0];
h qr[1];
h qr[2];
h qr[3];
h qr[4];
h qr[5];
h qr[6];
h qr[7];
h qr[8];
h qr[9];
h qr[10];
h qr[11];
h qr[12];
x qr[13];
h qr[13];
barrier qr[0],qr[1],qr[2],qr[3],qr[4],qr[5],qr[6],qr[7],qr[8],qr[9],qr[10],qr[11],qr[12],qr[13];
cx qr[0],qr[13];
cx qr[1],qr[13];
cx qr[2],qr[13];
cx qr[3],qr[13];
cx qr[4],qr[13];
cx qr[5],qr[13];
cx qr[6],qr[13];
cx qr[7],qr[13];
cx qr[8],qr[13];
cx qr[9],qr[13];
cx qr[10],qr[13];
cx qr[11],qr[13];
cx qr[12],qr[13];
barrier qr[0],qr[1],qr[2],qr[3],qr[4],qr[5],qr[6],qr[7],qr[8],qr[9],qr[10],qr[11],qr[12],qr[13];
h qr[0];
h qr[1];
h qr[2];
h qr[3];
h qr[4];
h qr[5];
h qr[6];
h qr[7];
h qr[8];
h qr[9];
h qr[10];
h qr[11];
h qr[12];
measure qr[0] -> cr[0];
measure qr[1] -> cr[1];
measure qr[2] -> cr[2];
measure qr[3] -> cr[3];
measure qr[4] -> cr[4];
measure qr[5] -> cr[5];
measure qr[6] -> cr[6];
measure qr[7] -> cr[7];
measure qr[8] -> cr[8];
measure qr[9] -> cr[9];
measure qr[10] -> cr[10];
measure qr[11] -> cr[11];
measure qr[12] -> cr[12];
" },
  { name := "bv_n19", category := "Bernstein-Vazirani", sourcePath := "medium/bv_n19/bv_n19.qasm",
    qubits := 19, hCount := 37, plusCount := 18, qasm := "//@author Raymond Harry Rudy rudyhar@jp.ibm.com
//Bernstein-Vazirani with 19 qubits.
//Hidden string is 111111111111111111
OPENQASM 2.0;
include \"qelib1.inc\";
qreg qr[19];
creg cr[18];
h qr[0];
h qr[1];
h qr[2];
h qr[3];
h qr[4];
h qr[5];
h qr[6];
h qr[7];
h qr[8];
h qr[9];
h qr[10];
h qr[11];
h qr[12];
h qr[13];
h qr[14];
h qr[15];
h qr[16];
h qr[17];
x qr[18];
h qr[18];
barrier qr[0],qr[1],qr[2],qr[3],qr[4],qr[5],qr[6],qr[7],qr[8],qr[9],qr[10],qr[11],qr[12],qr[13],qr[14],qr[15],qr[16],qr[17],qr[18];
cx qr[0],qr[18];
cx qr[1],qr[18];
cx qr[2],qr[18];
cx qr[3],qr[18];
cx qr[4],qr[18];
cx qr[5],qr[18];
cx qr[6],qr[18];
cx qr[7],qr[18];
cx qr[8],qr[18];
cx qr[9],qr[18];
cx qr[10],qr[18];
cx qr[11],qr[18];
cx qr[12],qr[18];
cx qr[13],qr[18];
cx qr[14],qr[18];
cx qr[15],qr[18];
cx qr[16],qr[18];
cx qr[17],qr[18];
barrier qr[0],qr[1],qr[2],qr[3],qr[4],qr[5],qr[6],qr[7],qr[8],qr[9],qr[10],qr[11],qr[12],qr[13],qr[14],qr[15],qr[16],qr[17],qr[18];
h qr[0];
h qr[1];
h qr[2];
h qr[3];
h qr[4];
h qr[5];
h qr[6];
h qr[7];
h qr[8];
h qr[9];
h qr[10];
h qr[11];
h qr[12];
h qr[13];
h qr[14];
h qr[15];
h qr[16];
h qr[17];
measure qr[0] -> cr[0];
measure qr[1] -> cr[1];
measure qr[2] -> cr[2];
measure qr[3] -> cr[3];
measure qr[4] -> cr[4];
measure qr[5] -> cr[5];
measure qr[6] -> cr[6];
measure qr[7] -> cr[7];
measure qr[8] -> cr[8];
measure qr[9] -> cr[9];
measure qr[10] -> cr[10];
measure qr[11] -> cr[11];
measure qr[12] -> cr[12];
measure qr[13] -> cr[13];
measure qr[14] -> cr[14];
measure qr[15] -> cr[15];
measure qr[16] -> cr[16];
measure qr[17] -> cr[17];
" },
  { name := "cat_n35", category := "Cat/GHZ", sourcePath := "large/cat_n35/cat_n35.qasm",
    qubits := 35, hCount := 1, plusCount := 34, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg q[35];
creg c[35];
creg meas[35];
h q[0];
cx q[0],q[1];
cx q[1],q[2];
cx q[2],q[3];
cx q[3],q[4];
cx q[4],q[5];
cx q[5],q[6];
cx q[6],q[7];
cx q[7],q[8];
cx q[8],q[9];
cx q[9],q[10];
cx q[10],q[11];
cx q[11],q[12];
cx q[12],q[13];
cx q[13],q[14];
cx q[14],q[15];
cx q[15],q[16];
cx q[16],q[17];
cx q[17],q[18];
cx q[18],q[19];
cx q[19],q[20];
cx q[20],q[21];
cx q[21],q[22];
cx q[22],q[23];
cx q[23],q[24];
cx q[24],q[25];
cx q[25],q[26];
cx q[26],q[27];
cx q[27],q[28];
cx q[28],q[29];
cx q[29],q[30];
cx q[30],q[31];
cx q[31],q[32];
cx q[32],q[33];
cx q[33],q[34];
barrier q[0],q[1],q[2],q[3],q[4],q[5],q[6],q[7],q[8],q[9],q[10],q[11],q[12],q[13],q[14],q[15],q[16],q[17],q[18],q[19],q[20],q[21],q[22],q[23],q[24],q[25],q[26],q[27],q[28],q[29],q[30],q[31],q[32],q[33],q[34];
measure q[0] -> meas[0];
measure q[1] -> meas[1];
measure q[2] -> meas[2];
measure q[3] -> meas[3];
measure q[4] -> meas[4];
measure q[5] -> meas[5];
measure q[6] -> meas[6];
measure q[7] -> meas[7];
measure q[8] -> meas[8];
measure q[9] -> meas[9];
measure q[10] -> meas[10];
measure q[11] -> meas[11];
measure q[12] -> meas[12];
measure q[13] -> meas[13];
measure q[14] -> meas[14];
measure q[15] -> meas[15];
measure q[16] -> meas[16];
measure q[17] -> meas[17];
measure q[18] -> meas[18];
measure q[19] -> meas[19];
measure q[20] -> meas[20];
measure q[21] -> meas[21];
measure q[22] -> meas[22];
measure q[23] -> meas[23];
measure q[24] -> meas[24];
measure q[25] -> meas[25];
measure q[26] -> meas[26];
measure q[27] -> meas[27];
measure q[28] -> meas[28];
measure q[29] -> meas[29];
measure q[30] -> meas[30];
measure q[31] -> meas[31];
measure q[32] -> meas[32];
measure q[33] -> meas[33];
measure q[34] -> meas[34];
" },
  { name := "ghz_n40", category := "Cat/GHZ", sourcePath := "large/ghz_n40/ghz_n40.qasm",
    qubits := 40, hCount := 1, plusCount := 39, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg q[40];
creg c[40];
creg meas[40];
h q[0];
cx q[0],q[1];
cx q[1],q[2];
cx q[2],q[3];
cx q[3],q[4];
cx q[4],q[5];
cx q[5],q[6];
cx q[6],q[7];
cx q[7],q[8];
cx q[8],q[9];
cx q[9],q[10];
cx q[10],q[11];
cx q[11],q[12];
cx q[12],q[13];
cx q[13],q[14];
cx q[14],q[15];
cx q[15],q[16];
cx q[16],q[17];
cx q[17],q[18];
cx q[18],q[19];
cx q[19],q[20];
cx q[20],q[21];
cx q[21],q[22];
cx q[22],q[23];
cx q[23],q[24];
cx q[24],q[25];
cx q[25],q[26];
cx q[26],q[27];
cx q[27],q[28];
cx q[28],q[29];
cx q[29],q[30];
cx q[30],q[31];
cx q[31],q[32];
cx q[32],q[33];
cx q[33],q[34];
cx q[34],q[35];
cx q[35],q[36];
cx q[36],q[37];
cx q[37],q[38];
cx q[38],q[39];
barrier q[0],q[1],q[2],q[3],q[4],q[5],q[6],q[7],q[8],q[9],q[10],q[11],q[12],q[13],q[14],q[15],q[16],q[17],q[18],q[19],q[20],q[21],q[22],q[23],q[24],q[25],q[26],q[27],q[28],q[29],q[30],q[31],q[32],q[33],q[34],q[35],q[36],q[37],q[38],q[39];
measure q[0] -> meas[0];
measure q[1] -> meas[1];
measure q[2] -> meas[2];
measure q[3] -> meas[3];
measure q[4] -> meas[4];
measure q[5] -> meas[5];
measure q[6] -> meas[6];
measure q[7] -> meas[7];
measure q[8] -> meas[8];
measure q[9] -> meas[9];
measure q[10] -> meas[10];
measure q[11] -> meas[11];
measure q[12] -> meas[12];
measure q[13] -> meas[13];
measure q[14] -> meas[14];
measure q[15] -> meas[15];
measure q[16] -> meas[16];
measure q[17] -> meas[17];
measure q[18] -> meas[18];
measure q[19] -> meas[19];
measure q[20] -> meas[20];
measure q[21] -> meas[21];
measure q[22] -> meas[22];
measure q[23] -> meas[23];
measure q[24] -> meas[24];
measure q[25] -> meas[25];
measure q[26] -> meas[26];
measure q[27] -> meas[27];
measure q[28] -> meas[28];
measure q[29] -> meas[29];
measure q[30] -> meas[30];
measure q[31] -> meas[31];
measure q[32] -> meas[32];
measure q[33] -> meas[33];
measure q[34] -> meas[34];
measure q[35] -> meas[35];
measure q[36] -> meas[36];
measure q[37] -> meas[37];
measure q[38] -> meas[38];
measure q[39] -> meas[39];
" },
  { name := "bv_n30", category := "Bernstein-Vazirani", sourcePath := "large/bv_n30/bv_n30.qasm",
    qubits := 30, hCount := 59, plusCount := 18, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg q0[30];
creg c0[30];
h q0[0];
h q0[1];
h q0[2];
h q0[3];
h q0[4];
h q0[5];
h q0[6];
h q0[7];
h q0[8];
h q0[9];
h q0[10];
h q0[11];
h q0[12];
h q0[13];
h q0[14];
h q0[15];
h q0[16];
h q0[17];
h q0[18];
h q0[19];
h q0[20];
h q0[21];
h q0[22];
h q0[23];
h q0[24];
h q0[25];
h q0[26];
h q0[27];
h q0[28];
x q0[29];
h q0[29];
barrier q0[0],q0[1],q0[2],q0[3],q0[4],q0[5],q0[6],q0[7],q0[8],q0[9],q0[10],q0[11],q0[12],q0[13],q0[14],q0[15],q0[16],q0[17],q0[18],q0[19],q0[20],q0[21],q0[22],q0[23],q0[24],q0[25],q0[26],q0[27],q0[28],q0[29];
cx q0[0],q0[29];
cx q0[4],q0[29];
cx q0[5],q0[29];
cx q0[7],q0[29];
cx q0[8],q0[29];
cx q0[10],q0[29];
cx q0[11],q0[29];
cx q0[13],q0[29];
cx q0[15],q0[29];
cx q0[17],q0[29];
cx q0[21],q0[29];
cx q0[22],q0[29];
cx q0[23],q0[29];
cx q0[24],q0[29];
cx q0[25],q0[29];
cx q0[26],q0[29];
cx q0[27],q0[29];
cx q0[28],q0[29];
barrier q0[0],q0[1],q0[2],q0[3],q0[4],q0[5],q0[6],q0[7],q0[8],q0[9],q0[10],q0[11],q0[12],q0[13],q0[14],q0[15],q0[16],q0[17],q0[18],q0[19],q0[20],q0[21],q0[22],q0[23],q0[24],q0[25],q0[26],q0[27],q0[28],q0[29];
h q0[0];
h q0[1];
h q0[2];
h q0[3];
h q0[4];
h q0[5];
h q0[6];
h q0[7];
h q0[8];
h q0[9];
h q0[10];
h q0[11];
h q0[12];
h q0[13];
h q0[14];
h q0[15];
h q0[16];
h q0[17];
h q0[18];
h q0[19];
h q0[20];
h q0[21];
h q0[22];
h q0[23];
h q0[24];
h q0[25];
h q0[26];
h q0[27];
h q0[28];
measure q0[0] -> c0[0];
measure q0[1] -> c0[1];
measure q0[2] -> c0[2];
measure q0[3] -> c0[3];
measure q0[4] -> c0[4];
measure q0[5] -> c0[5];
measure q0[6] -> c0[6];
measure q0[7] -> c0[7];
measure q0[8] -> c0[8];
measure q0[9] -> c0[9];
measure q0[10] -> c0[10];
measure q0[11] -> c0[11];
measure q0[12] -> c0[12];
measure q0[13] -> c0[13];
measure q0[14] -> c0[14];
measure q0[15] -> c0[15];
measure q0[16] -> c0[16];
measure q0[17] -> c0[17];
measure q0[18] -> c0[18];
measure q0[19] -> c0[19];
measure q0[20] -> c0[20];
measure q0[21] -> c0[21];
measure q0[22] -> c0[22];
measure q0[23] -> c0[23];
measure q0[24] -> c0[24];
measure q0[25] -> c0[25];
measure q0[26] -> c0[26];
measure q0[27] -> c0[27];
measure q0[28] -> c0[28];
" },
  { name := "cat_n65", category := "Cat/GHZ", sourcePath := "large/cat_n65/cat_n65.qasm",
    qubits := 65, hCount := 1, plusCount := 64, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg q[65];
creg c[65];
creg meas[65];
h q[0];
cx q[0],q[1];
cx q[1],q[2];
cx q[2],q[3];
cx q[3],q[4];
cx q[4],q[5];
cx q[5],q[6];
cx q[6],q[7];
cx q[7],q[8];
cx q[8],q[9];
cx q[9],q[10];
cx q[10],q[11];
cx q[11],q[12];
cx q[12],q[13];
cx q[13],q[14];
cx q[14],q[15];
cx q[15],q[16];
cx q[16],q[17];
cx q[17],q[18];
cx q[18],q[19];
cx q[19],q[20];
cx q[20],q[21];
cx q[21],q[22];
cx q[22],q[23];
cx q[23],q[24];
cx q[24],q[25];
cx q[25],q[26];
cx q[26],q[27];
cx q[27],q[28];
cx q[28],q[29];
cx q[29],q[30];
cx q[30],q[31];
cx q[31],q[32];
cx q[32],q[33];
cx q[33],q[34];
cx q[34],q[35];
cx q[35],q[36];
cx q[36],q[37];
cx q[37],q[38];
cx q[38],q[39];
cx q[39],q[40];
cx q[40],q[41];
cx q[41],q[42];
cx q[42],q[43];
cx q[43],q[44];
cx q[44],q[45];
cx q[45],q[46];
cx q[46],q[47];
cx q[47],q[48];
cx q[48],q[49];
cx q[49],q[50];
cx q[50],q[51];
cx q[51],q[52];
cx q[52],q[53];
cx q[53],q[54];
cx q[54],q[55];
cx q[55],q[56];
cx q[56],q[57];
cx q[57],q[58];
cx q[58],q[59];
cx q[59],q[60];
cx q[60],q[61];
cx q[61],q[62];
cx q[62],q[63];
cx q[63],q[64];
barrier q[0],q[1],q[2],q[3],q[4],q[5],q[6],q[7],q[8],q[9],q[10],q[11],q[12],q[13],q[14],q[15],q[16],q[17],q[18],q[19],q[20],q[21],q[22],q[23],q[24],q[25],q[26],q[27],q[28],q[29],q[30],q[31],q[32],q[33],q[34],q[35],q[36],q[37],q[38],q[39],q[40],q[41],q[42],q[43],q[44],q[45],q[46],q[47],q[48],q[49],q[50],q[51],q[52],q[53],q[54],q[55],q[56],q[57],q[58],q[59],q[60],q[61],q[62],q[63],q[64];
measure q[0] -> meas[0];
measure q[1] -> meas[1];
measure q[2] -> meas[2];
measure q[3] -> meas[3];
measure q[4] -> meas[4];
measure q[5] -> meas[5];
measure q[6] -> meas[6];
measure q[7] -> meas[7];
measure q[8] -> meas[8];
measure q[9] -> meas[9];
measure q[10] -> meas[10];
measure q[11] -> meas[11];
measure q[12] -> meas[12];
measure q[13] -> meas[13];
measure q[14] -> meas[14];
measure q[15] -> meas[15];
measure q[16] -> meas[16];
measure q[17] -> meas[17];
measure q[18] -> meas[18];
measure q[19] -> meas[19];
measure q[20] -> meas[20];
measure q[21] -> meas[21];
measure q[22] -> meas[22];
measure q[23] -> meas[23];
measure q[24] -> meas[24];
measure q[25] -> meas[25];
measure q[26] -> meas[26];
measure q[27] -> meas[27];
measure q[28] -> meas[28];
measure q[29] -> meas[29];
measure q[30] -> meas[30];
measure q[31] -> meas[31];
measure q[32] -> meas[32];
measure q[33] -> meas[33];
measure q[34] -> meas[34];
measure q[35] -> meas[35];
measure q[36] -> meas[36];
measure q[37] -> meas[37];
measure q[38] -> meas[38];
measure q[39] -> meas[39];
measure q[40] -> meas[40];
measure q[41] -> meas[41];
measure q[42] -> meas[42];
measure q[43] -> meas[43];
measure q[44] -> meas[44];
measure q[45] -> meas[45];
measure q[46] -> meas[46];
measure q[47] -> meas[47];
measure q[48] -> meas[48];
measure q[49] -> meas[49];
measure q[50] -> meas[50];
measure q[51] -> meas[51];
measure q[52] -> meas[52];
measure q[53] -> meas[53];
measure q[54] -> meas[54];
measure q[55] -> meas[55];
measure q[56] -> meas[56];
measure q[57] -> meas[57];
measure q[58] -> meas[58];
measure q[59] -> meas[59];
measure q[60] -> meas[60];
measure q[61] -> meas[61];
measure q[62] -> meas[62];
measure q[63] -> meas[63];
measure q[64] -> meas[64];
" },
  { name := "ghz_n78", category := "Cat/GHZ", sourcePath := "large/ghz_n78/ghz_n78.qasm",
    qubits := 78, hCount := 1, plusCount := 77, qasm := "OPENQASM 2.0;
include \"qelib1.inc\";
qreg q[78];
creg c[78];
creg meas[78];
h q[0];
cx q[0],q[1];
cx q[1],q[2];
cx q[2],q[3];
cx q[3],q[4];
cx q[4],q[5];
cx q[5],q[6];
cx q[6],q[7];
cx q[7],q[8];
cx q[8],q[9];
cx q[9],q[10];
cx q[10],q[11];
cx q[11],q[12];
cx q[12],q[13];
cx q[13],q[14];
cx q[14],q[15];
cx q[15],q[16];
cx q[16],q[17];
cx q[17],q[18];
cx q[18],q[19];
cx q[19],q[20];
cx q[20],q[21];
cx q[21],q[22];
cx q[22],q[23];
cx q[23],q[24];
cx q[24],q[25];
cx q[25],q[26];
cx q[26],q[27];
cx q[27],q[28];
cx q[28],q[29];
cx q[29],q[30];
cx q[30],q[31];
cx q[31],q[32];
cx q[32],q[33];
cx q[33],q[34];
cx q[34],q[35];
cx q[35],q[36];
cx q[36],q[37];
cx q[37],q[38];
cx q[38],q[39];
cx q[39],q[40];
cx q[40],q[41];
cx q[41],q[42];
cx q[42],q[43];
cx q[43],q[44];
cx q[44],q[45];
cx q[45],q[46];
cx q[46],q[47];
cx q[47],q[48];
cx q[48],q[49];
cx q[49],q[50];
cx q[50],q[51];
cx q[51],q[52];
cx q[52],q[53];
cx q[53],q[54];
cx q[54],q[55];
cx q[55],q[56];
cx q[56],q[57];
cx q[57],q[58];
cx q[58],q[59];
cx q[59],q[60];
cx q[60],q[61];
cx q[61],q[62];
cx q[62],q[63];
cx q[63],q[64];
cx q[64],q[65];
cx q[65],q[66];
cx q[66],q[67];
cx q[67],q[68];
cx q[68],q[69];
cx q[69],q[70];
cx q[70],q[71];
cx q[71],q[72];
cx q[72],q[73];
cx q[73],q[74];
cx q[74],q[75];
cx q[75],q[76];
cx q[76],q[77];
barrier q[0],q[1],q[2],q[3],q[4],q[5],q[6],q[7],q[8],q[9],q[10],q[11],q[12],q[13],q[14],q[15],q[16],q[17],q[18],q[19],q[20],q[21],q[22],q[23],q[24],q[25],q[26],q[27],q[28],q[29],q[30],q[31],q[32],q[33],q[34],q[35],q[36],q[37],q[38],q[39],q[40],q[41],q[42],q[43],q[44],q[45],q[46],q[47],q[48],q[49],q[50],q[51],q[52],q[53],q[54],q[55],q[56],q[57],q[58],q[59],q[60],q[61],q[62],q[63],q[64],q[65],q[66],q[67],q[68],q[69],q[70],q[71],q[72],q[73],q[74],q[75],q[76],q[77];
measure q[0] -> meas[0];
measure q[1] -> meas[1];
measure q[2] -> meas[2];
measure q[3] -> meas[3];
measure q[4] -> meas[4];
measure q[5] -> meas[5];
measure q[6] -> meas[6];
measure q[7] -> meas[7];
measure q[8] -> meas[8];
measure q[9] -> meas[9];
measure q[10] -> meas[10];
measure q[11] -> meas[11];
measure q[12] -> meas[12];
measure q[13] -> meas[13];
measure q[14] -> meas[14];
measure q[15] -> meas[15];
measure q[16] -> meas[16];
measure q[17] -> meas[17];
measure q[18] -> meas[18];
measure q[19] -> meas[19];
measure q[20] -> meas[20];
measure q[21] -> meas[21];
measure q[22] -> meas[22];
measure q[23] -> meas[23];
measure q[24] -> meas[24];
measure q[25] -> meas[25];
measure q[26] -> meas[26];
measure q[27] -> meas[27];
measure q[28] -> meas[28];
measure q[29] -> meas[29];
measure q[30] -> meas[30];
measure q[31] -> meas[31];
measure q[32] -> meas[32];
measure q[33] -> meas[33];
measure q[34] -> meas[34];
measure q[35] -> meas[35];
measure q[36] -> meas[36];
measure q[37] -> meas[37];
measure q[38] -> meas[38];
measure q[39] -> meas[39];
measure q[40] -> meas[40];
measure q[41] -> meas[41];
measure q[42] -> meas[42];
measure q[43] -> meas[43];
measure q[44] -> meas[44];
measure q[45] -> meas[45];
measure q[46] -> meas[46];
measure q[47] -> meas[47];
measure q[48] -> meas[48];
measure q[49] -> meas[49];
measure q[50] -> meas[50];
measure q[51] -> meas[51];
measure q[52] -> meas[52];
measure q[53] -> meas[53];
measure q[54] -> meas[54];
measure q[55] -> meas[55];
measure q[56] -> meas[56];
measure q[57] -> meas[57];
measure q[58] -> meas[58];
measure q[59] -> meas[59];
measure q[60] -> meas[60];
measure q[61] -> meas[61];
measure q[62] -> meas[62];
measure q[63] -> meas[63];
measure q[64] -> meas[64];
measure q[65] -> meas[65];
measure q[66] -> meas[66];
measure q[67] -> meas[67];
measure q[68] -> meas[68];
measure q[69] -> meas[69];
measure q[70] -> meas[70];
measure q[71] -> meas[71];
measure q[72] -> meas[72];
measure q[73] -> meas[73];
measure q[74] -> meas[74];
measure q[75] -> meas[75];
measure q[76] -> meas[76];
measure q[77] -> meas[77];
" },
]

/-- Representative QASMBench programs blocked by current exact-language semantics. -/
def blockedSuite : List BlockedCase := [
  { name := "shor_n5", category := "Shor", sourcePath := "small/shor_n5/shor_n5.qasm",
    blocker := "cswap/reset/dynamic if" },
  { name := "hhl_n7", category := "HHL", sourcePath := "small/hhl_n7/hhl_n7.qasm",
    blocker := "rx/ry/rz arbitrary rotations" },
  { name := "ising_n10", category := "Hamiltonian simulation", sourcePath := "small/ising_n10/ising_n10.qasm",
    blocker := "rz arbitrary rotations" },
  { name := "basis_trotter_n4", category := "Hamiltonian simulation", sourcePath := "small/basis_trotter_n4/basis_trotter_n4.qasm",
    blocker := "rx/ry/rz/u3/swap arbitrary rotations" },
  { name := "qaoa_n3", category := "QAOA/Hamiltonian", sourcePath := "small/qaoa_n3/qaoa_n3.qasm",
    blocker := "rx/rz arbitrary rotations" },
  { name := "qft_n4", category := "QFT", sourcePath := "small/qft_n4/qft_n4.qasm",
    blocker := "cu1 controlled arbitrary phase" },
]

/-! ## Compile-time benchmark gates

These use `#guard` rather than `#eval`, so a benchmark regression is a build failure and
successful builds stay quiet.
-/

#guard positiveSuite.length == 20
#guard positiveSuite.all compilesWithSeparatedBare
#guard positiveSuite.all compilesWithPackedBare
#guard (positiveSuite.filter (fun b => ! tMagicBench b)).all compilesPhysicallyWithSeparatedBare
#guard (positiveSuite.filter tMagicBench).all
  (fun b => ! compilesPhysicallyWithSeparatedBare b)

/-- Surface-code smoke: CX-only programs work with one surface block per logical. -/
def separatedSurfaceDecl (d i : Nat) : ChainQ.NamedCodeDecl :=
  surfaceDecl (logicalName "s" i) d ["data"]

def separatedSurfaceData (i : Nat) : NamedLogical :=
  { code := logicalName "s" i, logical := "data" }

def separatedSurfaceRequest (d n : Nat) : AllocationRequest :=
  { decls := (List.range n).map (separatedSurfaceDecl d),
    dataLogicals := (List.range n).map separatedSurfaceData,
    ancillas := [],
    cnotMode := .strictTransversal,
    cnotIncidence := some (idMat (ChainQ.surface d).n) }

def cxOnlyQASM : String := "qreg q[2]; cx q[0],q[1];"

#guard ok? (compileOpenQASM2ToMixIR? [] cxOnlyQASM (separatedSurfaceRequest 2 2))
#guard ok? (compileOpenQASM2ToMixIR? [] cxOnlyQASM (separatedSurfaceRequest 3 2))

/-- H on surface-code blocks is not yet an automatic positive benchmark. -/
def surfaceHBlockedQASM : String := "qreg q[1]; h q[0];"

#guard !(ok? (compileOpenQASM2ToMixIR? [] surfaceHBlockedQASM (separatedSurfaceRequest 2 1)))
#guard !(ok? (compileOpenQASM2ToMixIR? [] surfaceHBlockedQASM (separatedSurfaceRequest 3 1)))

end Compiler.QASM.Benchmarks
