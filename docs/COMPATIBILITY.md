# Compiler compatibility

The original development used Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The prepared project uses
Lean `v4.35.0-rc2` and Mathlib's matching release commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, with all dependencies fixed by
[lake-manifest.json](../lake-manifest.json).

Every original Lean source now begins with `module`, uses `public import`, and
places its previously public declarations in `@[expose] public section`.
Exposing definition bodies preserves their earlier reducibility and makes
the original definitional-equality proofs and instances available to clients.
These changes satisfy the current module requirement without altering the
mathematical definitions, hypotheses, conclusions, or proof scripts.

An exact byte comparison of all **642 mathematical source modules**, after
removing only these deterministic header/import/exposure additions, recovers
their original versions without whitespace normalization. The original hashes
and reproducible check are in [original-source-hashes.json](original-source-hashes.json)
and [check-compatibility.py](../scripts/check-compatibility.py). The audit module has an additional nonmathematical change:
it imports Solution and includes its declarations in the transitive axiom
inventory. Challenge and Solution are new interface modules.

The complete development retains its original names and library structure.
Compiler warnings about deprecated tactic names or unused arguments remain
visible during builds; they are separate from errors or proof holes. The
revision-specific build result is in [VERIFICATION.md](VERIFICATION.md).
