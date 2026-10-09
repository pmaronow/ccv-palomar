#!/usr/bin/env python3
"""Run the pinned Comparator with Palomar's two required independent kernels.

Generated configuration, transcripts, and the result record go outside the
repository. This is a local check, not a Palomar submission.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
KERNEL_ACCEPTANCE = {
    "con-ron": "con-ron kernel accepts the solution",
    "nanoda": "nanoda kernel accepts the solution",
    "leanchecker": "Lean default kernel accepts the solution",
}


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def source_record() -> dict[str, str]:
    pinned_files = {"lakefile.toml", "lakefile.lean", "lake-manifest.json",
                    "lean-toolchain", "comparator.json"}
    paths = []
    for directory, children, names in os.walk(ROOT):
        children[:] = sorted(name for name in children
                             if name not in {".git", ".lake", ".cache", "verification-run", "__pycache__"}
                             and not (Path(directory) / name).is_symlink())
        for name in names:
            if name.endswith(".lean") or name in pinned_files:
                path = Path(directory) / name
                if path.is_symlink():
                    raise ValueError(f"source must be a regular file: {path}")
                paths.append(path)
    return {str(path.relative_to(ROOT)): digest(path) for path in sorted(paths)}


def output(command: list[str]) -> str:
    return subprocess.check_output(command, cwd=ROOT, text=True).strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT.parent / (ROOT.name + "-verification-run") / "comparator")
    args = parser.parse_args()
    destination = args.output_dir.resolve()
    if destination.is_relative_to(ROOT) or ROOT.is_relative_to(destination):
        raise ValueError("the output directory must be outside the source repository")
    destination.mkdir(parents=True, exist_ok=True)

    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    if not isinstance(config, dict) or "external_kernels" in config:
        raise ValueError("comparator.json must be an object without external_kernels")
    for field in ("challenge_module", "solution_module", "theorem_names", "permitted_axioms"):
        if field not in config:
            raise ValueError(f"comparator.json is missing {field}")
    if set(config["permitted_axioms"]) != {"propext", "Quot.sound", "Classical.choice"}:
        raise ValueError("the permitted axioms must be exactly the three standard axioms")
    if shutil.which("bwrap") is None:
        raise ValueError("bubblewrap (bwrap) is required by the sandboxed Comparator")

    prefix = Path(output(["lean", "--print-prefix"]))
    tools = {name: prefix / "bin" / name for name in
             ("lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron")}
    for name, path in tools.items():
        if not path.is_file() or not os.access(path, os.X_OK):
            raise ValueError(f"the pinned toolchain does not bundle executable {name}")

    config.pop("enable_nanoda", None)
    config["external_kernels"] = {
        "nanoda": [str(tools["nanoda_bin"])],
        "con-ron": [str(tools["con-ron"]), "--jobs=2"],
    }
    protected_config = destination / "protected-comparator.json"
    protected_config.write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
    before = source_record()
    report = {
        "started_at": datetime.now(timezone.utc).isoformat(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "lean_version": output([str(tools["lean"]), "--version"]),
        "tools_sha256": {name: digest(path) for name, path in tools.items()},
        "source_sha256": before,
        "external_kernels": config["external_kernels"],
        "scope": "Local sandboxed Comparator, axiom audit, and exported-proof kernel checks",
    }
    if (ROOT / ".git").exists():
        revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                  text=True, capture_output=True)
        if revision.returncode == 0:
            report["git_revision"] = revision.stdout.strip()
        report["git_status"] = output(["git", "status", "--porcelain"])

    command = [str(tools["lake"]), "comparator", "--config", str(protected_config)]
    environment = dict(os.environ)
    environment["PATH"] = str(prefix / "bin") + os.pathsep + environment.get("PATH", "")
    environment["LEAN_ABORT_ON_PANIC"] = "1"
    accepted = {name: False for name in KERNEL_ACCEPTANCE}
    print("Running sandboxed Comparator, NanoDa, con-ron (--jobs=2), and leanchecker.", flush=True)
    with (destination / "comparator.log").open("w", encoding="utf-8") as transcript:
        process = subprocess.Popen(command, cwd=ROOT, env=environment, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert process.stdout is not None
        for line in process.stdout:
            transcript.write(line)
            transcript.flush()
            print(line, end="", flush=True)
            for name, marker in KERNEL_ACCEPTANCE.items():
                if line.strip() == marker:
                    accepted[name] = True
        returncode = process.wait()

    unchanged = before == source_record()
    success = returncode == 0 and unchanged and all(accepted.values())
    report.update({
        "finished_at": datetime.now(timezone.utc).isoformat(),
        "comparator_exit_code": returncode,
        "kernel_acceptance": accepted,
        "source_unchanged": unchanged,
        "passed": success,
    })
    (destination / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if not unchanged:
        print("Source changed during verification; rerun before claiming a pass.", file=sys.stderr)
    if returncode == 0 and not all(accepted.values()):
        print("A required kernel acceptance was not recorded; verification is incomplete.", file=sys.stderr)
    print(f"{'PASS' if success else 'INCOMPLETE OR FAILED'}: {destination / 'result.json'}", flush=True)
    return 0 if success else (returncode or 1)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Verification could not run: {error}", file=sys.stderr)
        raise SystemExit(2)
