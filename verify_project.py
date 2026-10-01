"""Reproduce the pinned whole-project build and the expanded original target.

This script records real process output. It does not repair proofs or assert
success before the compiler finishes. Requires Python 3 and elan/Lake on PATH.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--skip-cache", action="store_true",
                        help="Skip official Mathlib cache download when already present.")
    args = parser.parse_args()
    project = args.project.resolve()
    if args.threads < 1:
        parser.error("--threads must be positive")
    toolchain = (project / "lean-toolchain").read_text(encoding="utf-8").strip()
    expected_version = toolchain.rsplit(":v", 1)[-1]
    target = project / "VerifyOriginalStatement.lean"
    if not target.is_file():
        parser.error(f"Missing independent original statement: {target}")
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    logs = project / "verification_logs" / stamp
    logs.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, LEAN_NUM_THREADS=str(args.threads), PYTHONUTF8="1")

    def proof_snapshot() -> dict[str, str]:
        paths = set(project.glob("*.lean"))
        paths.update((project / "third_party").rglob("*.lean"))
        paths.update(project / name for name in ("lean-toolchain", "lake-manifest.json"))
        return {path.relative_to(project).as_posix():
                hashlib.sha256(path.read_bytes()).hexdigest()
                for path in sorted(paths) if path.is_file()}

    initial_sources = proof_snapshot()
    manifest = {
        "started_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "project": str(project), "declared_toolchain": toolchain,
        "lean_runtime_threads": args.threads, "steps": [],
        "status": "RUNNING", "verification_level": "Lean build and axiom inspection",
        "kernel_replay": "NOT RUN BY THIS SCRIPT",
        "proof_source_snapshot_sha256": initial_sources,
    }
    summary = logs / "verification.json"

    def save() -> None:
        summary.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n",
                           encoding="utf-8")

    def run(label: str, command: list[str]) -> tuple[int, str]:
        output_path = logs / f"{len(manifest['steps']) + 1:02d}-{label}.log"
        record = {"label": label, "command": command,
                  "started_at": dt.datetime.now(dt.timezone.utc).isoformat(),
                  "log": output_path.name}
        manifest["steps"].append(record)
        save()
        chunks: list[str] = []
        try:
            with output_path.open("w", encoding="utf-8", newline="\n") as out:
                process = subprocess.Popen(command, cwd=project, env=env,
                                           stdout=subprocess.PIPE,
                                           stderr=subprocess.STDOUT, text=True,
                                           encoding="utf-8", errors="replace")
                assert process.stdout is not None
                for line in process.stdout:
                    out.write(line)
                    out.flush()
                    print(line, end="", flush=True)
                    chunks.append(line)
                code = process.wait()
        except OSError as error:
            code = 127
            chunks.append(str(error) + "\n")
            output_path.write_text("".join(chunks), encoding="utf-8")
        record.update(exit_code=code, ended_at=dt.datetime.now(dt.timezone.utc).isoformat(),
                      log_sha256=hashlib.sha256(output_path.read_bytes()).hexdigest())
        save()
        return code, "".join(chunks)

    def fail(reason: str, code: int = 1) -> int:
        manifest.update(status="FAILED", reason=reason,
                        ended_at=dt.datetime.now(dt.timezone.utc).isoformat())
        save()
        print(f"FAILED: {reason}\nEvidence: {summary}", file=sys.stderr)
        return code or 1

    code, version = run("lean-version", ["lake", "env", "lean", "--version"])
    if code:
        return fail("Could not execute the declared Lean environment", code)
    if not re.search(r"\bversion\s+" + re.escape(expected_version) + r"(?:\D|$)", version):
        return fail("Executed Lean version differs from lean-toolchain")
    if not args.skip_cache:
        code, _ = run("official-mathlib-cache", ["lake", "exe", "cache", "get"])
        if code:
            return fail("Official pinned-version cache download failed", code)
    code, _ = run("whole-project-build", ["lake", "build", "JSP1006Proof"])
    if code:
        return fail("Whole-project Lean build failed", code)
    code, output = run("original-statement-and-axioms",
                       ["lake", "env", "lean", "VerifyOriginalStatement.lean"])
    if code:
        return fail("Expanded original statement or axiom commands failed", code)
    required = {"audit_erdos1201_original_statement", "Erdos1201.erdos_1201",
                "Erdos1201.erdos_1201_eventually",
                "audit_erdos1201_formalconjectures_statement"}
    records = re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    found = {name: sorted({item.strip() for item in names.split(",") if item.strip()})
             for name, names in records}
    manifest["axioms"] = found
    if not required.issubset(found):
        return fail("Missing actual axiom output for one or more final targets")
    standard = {"propext", "Classical.choice", "Quot.sound"}
    unexpected = {name: sorted(set(found[name]) - standard) for name in required
                  if set(found[name]) - standard}
    if unexpected:
        manifest["unexpected_axioms"] = unexpected
        return fail("Final targets depend on axioms outside the declared standard set")
    if proof_snapshot() != initial_sources:
        return fail("Proof sources or dependency declarations changed during verification")
    manifest.update(status="PASSED", ended_at=dt.datetime.now(dt.timezone.utc).isoformat())
    save()
    print(f"PASSED: full build, original statement, and final axiom outputs.\nEvidence: {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
