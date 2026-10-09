# Provenance and attribution

The mathematical source is *Nearly Minimax Variance Estimation Under Rough
Random Design*, Hexagon identifier `2610.00162v1`, by **P. M. Aronow and
Patrick Lopatto**. The authoritative manuscript sources are in [paper/](../paper/).
The earlier arXiv manuscript, `2607.13170v3`, has weaker bounds and is not
the source for the refined stretched-exponential bracket here.

The formalization authors and responsible maintainers are **P. M. Aronow and
Patrick Lopatto**, as designated for this project. This attribution does not
assert that either author has reviewed or understood every Lean statement or
proof. The paper's own authors' note describes assistance with its writing;
that note is preserved in [main.tex](../paper/main.tex).

**Sol 6.1** autoformalized the original Lean development. Subsequent **Codex**
work prepared the independent statement interface, updated compiler and
library compatibility, organized the repository, and performed automated
statement, axiom, build, and packaging reviews. These are separate stages.
No human mathematical review is established by this preparation. Automation
cost and original prompting history were not recorded.

The original development pinned Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The prepared development uses
the pins in [lean-toolchain](../lean-toolchain), [lakefile.toml](../lakefile.toml),
and [lake-manifest.json](../lake-manifest.json). Compiler repairs must preserve
the mathematical statements; [COMPATIBILITY.md](COMPATIBILITY.md) records the
actual changes.

`Vendor/RoughRegime/` contains 29 reused modules and their umbrella module
from the supplied development. These support analytic and probabilistic
arguments. Their different statistical model is not substituted for the
NearlyMinimax model. [vendor-provenance.json](vendor-provenance.json) records
original and prepared source hashes and whether each file changed. Existing
comments remain intact. See [NOTICE](../NOTICE) for licensing boundaries.

Historical build logs, upload records, and earlier coverage assertions are not
verification of this revision. Current check evidence is tied to a source
inventory digest in [VERIFICATION.md](VERIFICATION.md) and can be reproduced
with the tools in [scripts/](../scripts/).
