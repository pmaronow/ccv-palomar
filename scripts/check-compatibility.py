#!/usr/bin/env python3
"""Check exact preservation of original mathematical source bodies.

The only accepted migration changes are the leading module header, public
imports, and one exposed public section. No whitespace normalization is used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys


def original_bytes(prepared: bytes) -> bytes:
    prefix = b"module\n\n"
    section = b"\n@[expose] public section\n\n"
    if not prepared.startswith(prefix):
        raise ValueError("missing exact module header")
    content = prepared[len(prefix):]
    if content.count(section) != 1:
        raise ValueError("expected exactly one inserted exposed public section")
    content = content.replace(section, b"", 1)
    lines = content.splitlines(keepends=True)
    for i, line in enumerate(lines):
        if line.startswith(b"public import "):
            lines[i] = line[len(b"public "):]
    return b"".join(lines)


def verify(repo: Path) -> dict:
    baseline = json.loads((repo / "docs/original-source-hashes.json").read_text())
    if baseline.get("schema_version") != 1 or baseline.get("hash_algorithm") != "sha256":
        raise ValueError("unsupported source-hash schema")
    expected = baseline["sources"]
    actual = {
        str(path.relative_to(repo))
        for directory in (repo / "NearlyMinimax", repo / "Vendor")
        for path in directory.rglob("*.lean")
    } | {"NearlyMinimax.lean"}
    errors = []
    for name in sorted(set(expected) - actual):
        errors.append({"source": name, "error": "baseline source missing"})
    for name in sorted(actual - set(expected)):
        errors.append({"source": name, "error": "mathematical source absent from baseline"})
    checked = 0
    for name in sorted(set(expected) & actual):
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("invalid baseline source path")
        try:
            recovered = original_bytes((repo / relative).read_bytes())
            digest = hashlib.sha256(recovered).hexdigest()
            if digest != expected[name]:
                errors.append({"source": name, "error": "original source body changed"})
            else:
                checked += 1
        except ValueError as exc:
            errors.append({"source": name, "error": str(exc)})
    return {
        "schema_version": 1,
        "check": "exact_original_mathematical_source_preservation",
        "passed": not errors,
        "baseline_source_count": len(expected),
        "verified_source_count": checked,
        "normalization": "Only deterministic module/public-import/exposed-section header removal; no whitespace normalization.",
        "errors": errors,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    try:
        result = verify(args.repo.resolve())
    except (OSError, ValueError, KeyError) as exc:
        print(json.dumps({"passed": False, "error": str(exc)}, indent=2))
        return 1
    print(json.dumps(result, indent=2))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
