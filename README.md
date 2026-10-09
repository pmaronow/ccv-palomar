# Nearly minimax variance estimation under rough random design

This Lean project formalizes minimax bounds for estimating a **constant
conditional variance** in random-design regression. Its mathematical source is
*Nearly Minimax Variance Estimation Under Rough Random Design*, by
**P. M. Aronow and Patrick Lopatto**, included as [LaTeX source](paper/main.tex)
and a [PDF](paper/main.pdf).

The unknown design density is bounded above and away from zero without a
smoothness assumption. The regression has an `s`-Hölder extension to an open
neighborhood of the unit cube. Conditional error distributions may depend on
the covariate, with mean zero, a common variance, and bounded fourth moments.
Risk is minimax **root-mean-square error**, defined from extended nonnegative
squared-loss integrals over all measurable estimators.

## Results

For `s > 1` and `d > 4s`, write

\[
\lambda=\frac{2(s+1)}{d+4},\qquad
\Psi_n=n^{-\lambda}e^{-\kappa\sqrt{\log n}}
           (\log n)^{(s-1)/(d+4)}.
\]

The project proves `c Ψ_n ≤ r_n ≤ C Ψ_n (log n)^Γ`, with the paper's exact
density-dependent `κ` and polynomial-dimension gap `Γ`. The constants and
sample-size threshold precede the quantifier over all open extension domains.
The bracket identifies the minimax exponent and leading stretched-exponential
factor, while leaving the precise logarithmic power unresolved.

| Paper result | Submission declaration in `NearlyMinimax.Submission` |
| --- | --- |
| Theorem 1.1: refined minimax bracket | `paper_main` |
| Corollary 1.2: exponent limit | `exponent_limit` |
| Corollary 1.2: eventual polynomial bounds | `polynomial_bounds` |
| Theorem 1.3: `max(n^(-1/2), n^(-4s/(d+4s)))` for `0 < s ≤ 1`, every `n ≥ 1` | `low_smoothness` |
| Theorem 1.4: `n^(-1/2)` for `s > 1`, `d ≤ 4s`, every `n ≥ 1` | `parametric` |

[Challenge.lean](Challenge.lean) is the independent statement interface. It
imports Mathlib and Lean core, provides concrete model, loss and rate definitions, and
contains five intentional theorem `sorry` placeholders.
[Solution.lean](Solution.lean) supplies the corresponding proofs.
[comparator.json](comparator.json) selects all five statements with no
definition holes; their transitive definition bodies must match.

The substantive development also proves separate sharp upper and lower
bounds, constructs estimators and lower-bound witnesses, and derives further
asymptotic consequences. [Mathematical fidelity](docs/FIDELITY.md) and
[numbered coverage](docs/COVERAGE.md) explain exact targets, representations,
alternative constructions, conditional infrastructure, and limitations.

## Installation and build

Install [elan](https://github.com/leanprover/elan), Git, and Python 3.11 or later.
The project pins **Lean 4.35.0-rc2** and **Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`**. The committed
[Lake manifest](lake-manifest.json) fixes all nine Git dependencies.

From the repository root:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The first command fetches dependencies and Mathlib's compiled cache. The build
includes the original library, reused RoughRegime library, Challenge and
Solution. `Audit.lean` checks every declaration in all original and reused
modules and Solution, including generated declarations and definitions, and
rejects custom axioms or transitive dependencies beyond `propext`,
`Classical.choice`, and `Quot.sound`. Challenge is excluded from this proof audit.

## Reproducible verification

The complete local verifier checks metadata against Palomar's pinned upstream
validator and the community v0.4 schema; repository structure, dependency pins,
source limits, and Challenge imports; the build and axiom inventory; and
Comparator with Lean's kernel, NanoDa, and con-ron. Install Python packages
`PyYAML==6.0.3` and `jsonschema==4.26.0`, and Linux `bubblewrap` (`bwrap`)
for Comparator.
SPDX detection uses Ruby/Bundler and the locked `licensee` dependencies in the
pinned PalomarSubmission checkout. Bootstrap that detector once:

```sh
git clone https://github.com/PalomarRegistry/PalomarSubmission ../palomar-tools
git -C ../palomar-tools checkout d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44
BUNDLE_GEMFILE=../palomar-tools/Gemfile bundle install
python3 scripts/verify.py --work-dir ../verification-run --paper
```

The verifier obtains its own pinned validator checkouts outside the source
tree. Bundler uses their identical locked Gemfile. Alternatively, pass
`--licensee-image IMAGE` for an existing Docker image containing that pinned
detector. Missing prerequisites or any failed check make verification
incomplete and produce a nonzero exit status.

For Comparator alone after the build:

```sh
python3 scripts/verify-comparator.py --output-dir ../verification-run/comparator
```

The wrapper generates a protected configuration registering bundled NanoDa
and con-ron (`--jobs=2`), checks all three kernel acceptance messages, and
records source and tool hashes. The submitted configuration contains no
`external_kernels` field. [VERIFICATION.md](docs/VERIFICATION.md) identifies
the exact checked inputs and completed checks. Raw logs, tool checkouts and
caches are generated outside the public source tree. These local checks are
separate from Palomar's hosted verification and editorial review.

The paper can be rebuilt with TeX Live and `latexmk -pdf main.tex` in `paper/`;
`verify.py --paper` builds it in the external verification directory.

## Scope and attribution

The low-smoothness and parametric submission statements fix the extension
domain before choosing their constants; they do not separately certify a
constant uniform over every extension domain. Some abstract auxiliary lemmas
have explicit primitive assumptions or a countably generated observation-space
condition. The coverage inventory distinguishes those results from complete
statistical endpoints. It does not claim independently certified literal
coverage of every clause of all 32 numbered paper blocks.

The exact logarithmic power, optimized constants, useful explicit thresholds,
and moderate-sample performance remain outside the proved claims. The model
and strict nondegeneracy margins are substantive restrictions.

Formalization authors and responsible maintainers: **P. M. Aronow and
Patrick Lopatto**. **Sol 6.1** autoformalized the original development.
Subsequent **Codex** preparation, compiler compatibility work and automated
review are disclosed separately in [PROVENANCE.md](docs/PROVENANCE.md) and
[formalization.yaml](formalization.yaml). No human mathematical review is
inferred from authorship or responsibility.

Original code and repository documentation, including the bundled RoughRegime
sources, use the [MIT license](LICENSE). Existing source comments are preserved;
[NOTICE](NOTICE) records source and dependency licensing boundaries.
