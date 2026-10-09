#!/usr/bin/env python3
"""Run revision-bound local checks; leave results and raw logs outside source."""
import argparse
import datetime
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from snapshot import ROOT, digest, inputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, default=ROOT.parent / (ROOT.name + "-verification-run"))
    parser.add_argument("--skip-cache", action="store_true",
                        help="Use installed dependencies without downloading Mathlib's cache")
    parser.add_argument("--paper", action="store_true", help="Also compile the paper using latexmk")
    parser.add_argument("--licensee-image", help="Optional image with Palomar's pinned licensee detector")
    args = parser.parse_args()
    work = args.work_dir.resolve()
    if work.is_relative_to(ROOT) or ROOT.is_relative_to(work):
        parser.error("work directory must be outside the source root and must not contain it")
    work.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env.setdefault("MATHLIB_CACHE_DIR", str(work / "mathlib-cache"))
    before = inputs()
    summary = {"input_sha256": digest(before), "checks": {},
               "time_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (work / "inputs.json").write_text(json.dumps(before, indent=2) + "\n")

    def run(name, command, cwd=ROOT):
        print(f"Checking {name}...", flush=True)
        with (work / f"{name}.log").open("w") as log:
            result = subprocess.run(command, cwd=cwd, env=env, stdout=log,
                                    stderr=subprocess.STDOUT)
        summary["checks"][name] = {"passed": result.returncode == 0,
                                    "exit_code": result.returncode}
        (work / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(f"{name} failed; see {work / (name + '.log')}")

    run("compatibility", [sys.executable, "scripts/check-compatibility.py"])
    if not args.skip_cache:
        run("cache", ["lake", "exe", "cache", "get"])
    preflight = [sys.executable, "scripts/palomar-preflight.py",
                 "--tools-dir", str(work / "policy-cache"),
                 "--report", str(work / "preflight.json")]
    if args.licensee_image:
        preflight.extend(["--licensee-image", args.licensee_image])
    run("preflight", preflight)
    run("build", ["lake", "build"])
    run("axioms", ["lake", "env", "lean", "Audit.lean"])
    audits = []
    for line in (work / "axioms.log").read_text().splitlines():
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(row, dict) and row.get("axiom_audit_passed") is True:
            audits.append(row)
    if len(audits) != 1:
        raise RuntimeError("Expected exactly one successful transitive axiom audit")
    audit = audits[0]
    own_modules = {"NearlyMinimax", "Solution"} | {
        str(p.relative_to(ROOT).with_suffix("")).replace("/", ".")
        for p in (ROOT / "NearlyMinimax").rglob("*.lean")}
    vendor_modules = {str(p.relative_to(ROOT / "Vendor").with_suffix("")).replace("/", ".")
                      for p in (ROOT / "Vendor").rglob("*.lean")}
    if set(audit["nearly_minimax_modules"]) != own_modules:
        raise RuntimeError("Axiom audit does not cover exactly all original and Solution modules")
    if set(audit["vendored_modules"]) != vendor_modules:
        raise RuntimeError("Axiom audit does not cover exactly all bundled vendor modules")
    selected = json.loads((ROOT / "comparator.json").read_text())["theorem_names"]
    theorems = {r["theorem"]: r["axioms"] for r in audit["theorems"]}
    if not set(selected) <= theorems.keys():
        raise RuntimeError("Selected Solution declarations missing from axiom audit")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if set(audit["allowed_axioms"]) != allowed or any(
            not set(axioms) <= allowed for axioms in theorems.values()):
        raise RuntimeError("Forbidden transitive axiom in proof inventory")
    (work / "axiom-inventory.json").write_text(json.dumps(audit, indent=2) + "\n")
    summary["axiom_inventory"] = {key: audit[key] for key in (
        "project_module_count", "declaration_count", "theorem_count", "allowed_axioms")}
    summary["selected_axioms"] = {name: theorems[name] for name in selected}
    run("comparator", [sys.executable, "scripts/verify-comparator.py",
                       "--output-dir", str(work / "comparator")])
    if args.paper:
        if not shutil.which("latexmk"):
            raise RuntimeError("latexmk is required for --paper")
        paper = work / "paper"
        shutil.copytree(ROOT / "paper", paper, dirs_exist_ok=True)
        run("paper", ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
                      "main.tex"], cwd=paper)
    if inputs() != before:
        raise RuntimeError("Verification inputs changed during the run")
    summary["input_unchanged"] = True
    summary["passed"] = True
    (work / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"All local checks completed for input digest {summary['input_sha256']}.")
    print(f"Evidence: {work / 'summary.json'}")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        print(f"Verification incomplete: {error}", file=sys.stderr)
        raise SystemExit(1)
