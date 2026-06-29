#!/usr/bin/env python3
"""Run normalized OpenQASM-2 files through the Lean QASM compiler pipeline.

This is a benchmark/probe driver, not a trusted compiler component. It generates a
temporary Lean file that imports `Compiler.QASM.Physical`, reads each QASM file from
disk, allocates one separated bare ChainQ logical block per virtual qubit, and calls
either `compileOpenQASM2ToMixIR?` or `compileOpenQASM2ToQClifford?`.

The default `--stage physical` is the honest full currently-wired path:
QASM -> allocation -> checked MixedIR -> verified structural QStab plus one
resident-code stabilizer extraction pass -> QClifford extraction. T/magic, code
switching, repeated syndrome rounds/decoding, and non-structural PPM are reported
as physical blockers/deferred work rather than silently accepted.

Example:

  python scripts/qasm_compile_lean_probe.py \
    outputs/qasm_normalized_logicq_alias/qaoa_n3__qaoa_n3__logicq-alias.qasm \
    outputs/qasm_normalized_logicq_alias/qft_n4__qft_n4__logicq-alias.qasm
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path


QREG_RE = re.compile(r"^\s*qreg\s+([A-Za-z_][A-Za-z0-9_]*)\[(\d+)\]\s*;", re.MULTILINE)


def infer_qubits(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    sizes = [int(m.group(2)) for m in QREG_RE.finditer(text)]
    if not sizes:
        raise ValueError(f"{path}: no qreg declaration found")
    return sum(sizes)


def lean_string(path: Path) -> str:
    # Forward slashes work for Lean/Windows paths and avoid backslash escaping surprises.
    return json.dumps(path.resolve().as_posix())


def render_probe(cases: list[tuple[Path, int]], stage: str) -> str:
    rows = ",\n".join(f"    ({lean_string(path)}, {qubits})" for path, qubits in cases)
    return f"""import Compiler.QASM.Physical

open Compiler.QASM

def logicalName (pref : String) (i : Nat) : String := pref ++ toString i

def separatedBareDecl (i : Nat) : ChainQ.NamedCodeDecl :=
  {{ ChainQ.indexedBareDecl with name := logicalName "q" i }}

def separatedBareData (i : Nat) : NamedLogical :=
  {{ code := logicalName "q" i, logical := "data" }}

def separatedBareRequest (n : Nat) : AllocationRequest :=
  {{ decls := (List.range n).map separatedBareDecl,
    dataLogicals := (List.range n).map separatedBareData,
    ancillas := [],
    cnotMode := .strictTransversal,
    cnotIncidence := some [[true]] }}

def parsedQASMOpCount (src : String) : Nat :=
  match parseOpenQASM2? src with
  | .ok p => p.opCount
  | .error _ => 0

def runMixed (path : String) (qubits : Nat) (src : String) : IO Unit := do
  match compileOpenQASM2ToMixIR? [] src (separatedBareRequest qubits) with
  | .ok a =>
      IO.println s!"ok_mixedir\\t{{path}}\\tqubits={{qubits}}\\tqasm_ops={{parsedQASMOpCount src}}\\tlogicq_ops={{a.alloc.prog.ops.length}}\\tmixed_steps={{a.compiled.steps.length}}\\tmeas={{a.alloc.measMap.length}}\\tobligations={{a.obligations.length}}"
  | .error e =>
      IO.println s!"error_mixedir\\t{{path}}\\tqubits={{qubits}}\\t{{repr e}}"

def runPhysical (path : String) (qubits : Nat) (src : String) : IO Unit := do
  match compileOpenQASM2ToQClifford? [] src (separatedBareRequest qubits) with
  | .ok a =>
      IO.println s!"ok_physical\\t{{path}}\\tqubits={{qubits}}\\tqasm_ops={{parsedQASMOpCount src}}\\tlogicq_ops={{a.qasm.alloc.prog.ops.length}}\\tmixed_steps={{a.mixed.length}}\\tsyndrome_instr={{a.syndrome.length}}\\tlogical_qstab_instr={{a.logicalQStab.length}}\\tqstab_instr={{a.qstab.length}}\\tqclifford_gates={{QClifford.Circuit.gateCount a.qclifford}}\\twidth={{QClifford.Circuit.width a.qclifford}}\\tmeas={{QClifford.Circuit.measCount a.qclifford}}\\ttwoq={{QClifford.Circuit.twoQubitCount a.qclifford}}\\tobligations={{a.qasm.obligations.length}}"
  | .error e =>
      IO.println s!"error_physical\\t{{path}}\\tqubits={{qubits}}\\t{{repr e}}"

def runProbeCases : List (Prod String Nat) -> IO Unit
  | [] => pure ()
  | c :: rest => do
      let path := c.1
      let qubits := c.2
      let src <- IO.FS.readFile path
      match "{stage}" with
      | "mixedir" => runMixed path qubits src
      | "physical" => runPhysical path qubits src
      | "both" => runMixed path qubits src *> runPhysical path qubits src
      | _ => IO.println s!"error_driver\\t{{path}}\\tunknown stage"
      runProbeCases rest

#eval runProbeCases [
{rows}
  ]
"""


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=Path, help="Normalized OpenQASM-2 files")
    parser.add_argument("--workspace", type=Path, default=Path.cwd(), help="LogicQ workspace root")
    parser.add_argument(
        "--stage",
        choices=("mixedir", "physical", "both"),
        default="physical",
        help="Pipeline stage to probe; physical is the default checked QClifford path",
    )
    parser.add_argument("--timeout", type=int, default=600, help="Seconds before killing Lean")
    parser.add_argument("--keep-probe", action="store_true", help="Keep the generated temporary Lean file")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    cases: list[tuple[Path, int]] = []
    for path in args.inputs:
        cases.append((path, infer_qubits(path)))

    probe = render_probe(cases, args.stage)
    tmp = tempfile.NamedTemporaryFile("w", suffix=".lean", encoding="utf-8", delete=False)
    try:
        tmp.write(probe)
        tmp.close()
        cmd = ["lake", "env", "lean", tmp.name]
        proc = subprocess.run(
            cmd,
            cwd=args.workspace,
            text=True,
            capture_output=True,
            timeout=args.timeout,
            check=False,
        )
        if proc.stdout:
            print(proc.stdout, end="")
        if proc.stderr:
            print(proc.stderr, end="", file=sys.stderr)
        if proc.returncode != 0:
            return proc.returncode
        error_prefixes = ("error_mixedir\t", "error_physical\t", "error_driver\t")
        return 2 if any(line.startswith(error_prefixes) for line in proc.stdout.splitlines()) else 0
    finally:
        if args.keep_probe:
            print(f"probe={tmp.name}", file=sys.stderr)
        else:
            Path(tmp.name).unlink(missing_ok=True)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
