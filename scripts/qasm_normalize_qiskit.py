#!/usr/bin/env python3
"""Normalize OpenQASM-2 inputs through Qiskit for the LogicQ QASM front-end.

This script is intentionally outside Lean.  Qiskit handles source-language
compatibility and basis synthesis; Lean then checks the fixed-basis output
against LogicQ's logical-resource contract.

Examples:

  python scripts/qasm_normalize_qiskit.py \
    --out-dir outputs/qasm_normalized \
    --basis logicq-alias \
    outputs/QASMBench/small/qft_n4/qft_n4.qasm

  python scripts/qasm_normalize_qiskit.py \
    --out-dir outputs/qasm_normalized_exact \
    --basis logicq \
    --max-output-gates 250000 \
    outputs/QASMBench/small/qaoa_n3/qaoa_n3.qasm

The `logicq-alias` basis keeps Qiskit's compact `sdg` / `tdg` gates.  The Lean
parser expands those exact aliases to `s;s;s` and `t` repeated seven times.
The `logicq` basis asks Qiskit to emit only the primitive LogicQ gate names.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

import qiskit
from qiskit import QuantumCircuit, transpile
from qiskit import qasm2


BASIS_GATES = {
    "logicq": ["h", "s", "t", "x", "z", "cx", "cz", "measure"],
    "logicq-alias": ["h", "s", "sdg", "t", "tdg", "x", "z", "cx", "cz", "measure"],
    "rotation": ["h", "s", "x", "z", "rx", "ry", "rz", "cx", "cz", "measure"],
    "u3": ["u3", "cx", "measure"],
}

LEAN_ACCEPTED = {
    "logicq": {"h", "s", "t", "x", "z", "cx", "cz", "measure", "barrier"},
    "logicq-alias": {
        "h",
        "s",
        "sdg",
        "t",
        "tdg",
        "x",
        "z",
        "cx",
        "cz",
        "measure",
        "barrier",
    },
    "rotation": {"h", "s", "x", "z", "rx", "ry", "rz", "cx", "cz", "measure", "barrier"},
    "u3": {"u3", "cx", "measure", "barrier"},
}

APPROX_SOURCE_OPS = {
    "rx",
    "ry",
    "rz",
    "u1",
    "u2",
    "u3",
    "u",
    "p",
    "cp",
    "cu1",
    "cu3",
    "rzz",
    "rxx",
    "ryy",
}

DYNAMIC_OR_STATEFUL_OPS = {
    "if_else",
    "while_loop",
    "for_loop",
    "switch_case",
    "break_loop",
    "continue_loop",
    "reset",
}


@dataclass
class CaseReport:
    source: str
    output: str | None
    status: str
    basis: str
    basis_gates: list[str]
    qiskit_version: str
    optimization_level: int
    approximation_degree: float | None
    source_qubits: int | None = None
    source_clbits: int | None = None
    source_ops: dict[str, int] | None = None
    output_ops: dict[str, int] | None = None
    output_gate_count: int | None = None
    unsupported_output_ops: list[str] | None = None
    dynamic_or_stateful_ops: list[str] | None = None
    approximation_obligation: bool = False
    wrote_qasm: bool = False
    error: str | None = None


def safe_stem(path: Path, basis: str) -> str:
    parent = path.parent.name
    stem = path.stem
    raw = f"{parent}__{stem}__{basis}"
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", raw)


def op_counts(circuit: QuantumCircuit) -> dict[str, int]:
    return {str(k): int(v) for k, v in circuit.count_ops().items()}


def total_ops(counts: dict[str, int]) -> int:
    return sum(counts.values())


def sorted_intersection(names: Iterable[str], allowed: set[str]) -> list[str]:
    return sorted(name for name in names if name in allowed)


def normalize_one(path: Path, args: argparse.Namespace) -> CaseReport:
    basis_gates = BASIS_GATES[args.basis]
    accepted = LEAN_ACCEPTED[args.basis]
    report = CaseReport(
        source=str(path),
        output=None,
        status="started",
        basis=args.basis,
        basis_gates=basis_gates,
        qiskit_version=getattr(qiskit, "__version__", "unknown"),
        optimization_level=args.optimization_level,
        approximation_degree=args.approximation_degree,
    )

    try:
        circuit = QuantumCircuit.from_qasm_file(str(path))
    except Exception as exc:  # noqa: BLE001 - report tool should not hide the original class.
        report.status = "load_error"
        report.error = f"{type(exc).__name__}: {exc}"
        return report

    report.source_qubits = circuit.num_qubits
    report.source_clbits = circuit.num_clbits
    report.source_ops = op_counts(circuit)
    report.approximation_obligation = bool(set(report.source_ops).intersection(APPROX_SOURCE_OPS))

    transpile_kwargs = {
        "basis_gates": basis_gates,
        "optimization_level": args.optimization_level,
    }
    if args.approximation_degree is not None:
        transpile_kwargs["approximation_degree"] = args.approximation_degree

    try:
        normalized = transpile(circuit, **transpile_kwargs)
    except Exception as exc:  # noqa: BLE001
        report.status = "transpile_error"
        report.error = f"{type(exc).__name__}: {exc}"
        return report

    output_counts = op_counts(normalized)
    report.output_ops = output_counts
    report.output_gate_count = total_ops(output_counts)
    report.unsupported_output_ops = sorted(name for name in output_counts if name not in accepted)
    report.dynamic_or_stateful_ops = sorted_intersection(output_counts.keys(), DYNAMIC_OR_STATEFUL_OPS)

    if report.output_gate_count > args.max_output_gates and not args.write_large:
        report.status = "skipped_too_large"
        report.error = (
            f"output has {report.output_gate_count} ops; pass --write-large or raise "
            "--max-output-gates to write the QASM file"
        )
        return report

    out_path = args.out_dir / f"{safe_stem(path, args.basis)}.qasm"
    try:
        qasm = qasm2.dumps(normalized)
        out_path.write_text(qasm, encoding="utf-8", newline="\n")
    except Exception as exc:  # noqa: BLE001
        report.status = "export_error"
        report.error = f"{type(exc).__name__}: {exc}"
        return report

    report.output = str(out_path)
    report.wrote_qasm = True
    report.status = "ok" if not report.unsupported_output_ops else "ok_with_residuals"
    return report


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=Path, help="OpenQASM-2 files to normalize")
    parser.add_argument("--out-dir", type=Path, required=True, help="Directory for normalized QASM")
    parser.add_argument(
        "--basis",
        choices=sorted(BASIS_GATES),
        default="logicq-alias",
        help="Target basis family",
    )
    parser.add_argument("--optimization-level", type=int, default=0, choices=range(4))
    parser.add_argument("--approximation-degree", type=float, default=None)
    parser.add_argument(
        "--max-output-gates",
        type=int,
        default=250_000,
        help="Skip writing outputs above this many operations unless --write-large is set",
    )
    parser.add_argument("--write-large", action="store_true", help="Write very large QASM outputs")
    parser.add_argument(
        "--manifest",
        type=Path,
        default=None,
        help="Manifest JSON path (default: OUT_DIR/manifest.json)",
    )
    parser.add_argument(
        "--fail-on-residual",
        action="store_true",
        help="Exit nonzero if any normalized output still has non-Lean operations",
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    manifest = args.manifest or (args.out_dir / "manifest.json")

    reports = [normalize_one(path, args) for path in args.inputs]
    payload = {
        "tool": "scripts/qasm_normalize_qiskit.py",
        "qiskit_version": getattr(qiskit, "__version__", "unknown"),
        "basis": args.basis,
        "basis_gates": BASIS_GATES[args.basis],
        "reports": [asdict(r) for r in reports],
    }
    manifest.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    for report in reports:
        residual = ""
        if report.unsupported_output_ops:
            residual = f" residual={','.join(report.unsupported_output_ops)}"
        approx = " approx" if report.approximation_obligation else ""
        output = f" -> {report.output}" if report.output else ""
        print(f"{report.status:18} {report.source}{output}{residual}{approx}")

    bad_status = [r for r in reports if r.status not in {"ok", "ok_with_residuals"}]
    bad_residual = [r for r in reports if r.unsupported_output_ops]
    if bad_status:
        return 2
    if args.fail_on_residual and bad_residual:
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
