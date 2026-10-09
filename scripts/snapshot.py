#!/usr/bin/env python3
"""Content-address the inputs used by the mathematical and build checks."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def inputs(root=ROOT):
    paths = [root / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "comparator.json",
        "formalization.yaml", "LICENSE", "NOTICE", "docs/original-source-hashes.json",
        "NearlyMinimax.lean", "Challenge.lean",
        "Solution.lean", "Audit.lean")]
    for directory, pattern in (("NearlyMinimax", "*.lean"), ("Vendor", "*.lean"),
                               ("scripts", "*.py"), ("paper", "*.tex"),
                               ("paper", "*.bib")):
        paths.extend((root / directory).rglob(pattern))
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(paths))}


def digest(manifest):
    return hashlib.sha256(json.dumps(manifest, sort_keys=True, separators=(",", ":"))
                          .encode("utf-8")).hexdigest()


if __name__ == "__main__":
    manifest = inputs()
    print(json.dumps({"algorithm": "sha256 of canonical sorted JSON input map",
                      "input_sha256": digest(manifest), "files": manifest}, indent=2))
