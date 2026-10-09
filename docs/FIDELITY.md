# Mathematical fidelity and scope

This document records an automated review of the mathematical statements and definitions in [the paper](../paper/body.tex) against the Lean source. It does not record human mathematical review. Authorship and maintainer responsibility do not imply review or approval of the formalization. Mechanical verification of a particular source revision is reported separately in [VERIFICATION.md](VERIFICATION.md).

The paper is *Nearly Minimax Variance Estimation Under Rough Random Design*, by P. M. Aronow and Patrick Lopatto. The repository includes its [main source](../paper/main.tex), [mathematical body](../paper/body.tex), and [PDF](../paper/main.pdf). [PROVENANCE.md](PROVENANCE.md) records attribution and source provenance. The correspondence below concerns this paper's constant conditional variance model.

## Selected results

[Challenge.lean](../Challenge.lean) gives concrete definitions and five independently readable statement targets using Mathlib alone. Its theorem `sorry` placeholders are intentional. [Solution.lean](../Solution.lean) repeats the statements and supplies proofs using the substantive development. The table identifies the original endpoints used by Solution and the corresponding paper results.

| Paper result | Original endpoint | Correspondence |
| --- | --- | --- |
| Theorem 1.1, the minimax bracket | [`paper_main`](../NearlyMinimax/PaperMain.lean) | The logarithmic-gap bracket with the exact exponent, stretched-exponential constant, and logarithmic powers. Positive constants and the common threshold precede every open extension domain and sample size. |
| Corollary 1.2, exponent limit | [`paper_exponent_limit`](../NearlyMinimax/PaperMain.lean) | The limit of `-log(r_n)/log(n)` is `2(s+1)/(d+4)` for `s>1`, `d>4s`. |
| Corollary 1.2, polynomial bounds | [`paper_polynomial_bounds`](../NearlyMinimax/PaperMain.lean) | Both eventual polynomial bounds. The formal statement chooses its positive constants before every positive epsilon, which is stronger than allowing the lower constant to depend on epsilon; the eventual threshold may depend on epsilon. |
| Theorem 1.3, low smoothness | [`paper_low_smoothness`](../NearlyMinimax/PaperLowSmoothness.lean) | A common constant and its reciprocal bracket `max(n^(-1/2), n^(-4s/(d+4s)))` for every `n≥1`, `0<s≤1`, and every positive integer dimension. Includes `s=1`, `n=1`, and `d=4s`. |
| Theorem 1.4, parametric regime | [`paper_parametric`](../NearlyMinimax/PaperParametric.lean) | A common constant and its reciprocal bracket the root-n scale for every `n≥1`, `s>1`, `d≤4s`, including the critical dimension. |

The bracket comes from two separate statistical bounds. [`paper_upper_sharp_estimator` and `paper_upper_sharp`](../NearlyMinimax/PaperSharpUpper.lean) correspond to Theorem 3.1; the former supplies a measurable estimator and its risk bound, and the latter takes the minimax infimum. [`paper_lower_sharp`](../NearlyMinimax/PaperLowerSharp.lean) corresponds to Theorem 6.1 and has no assumed spatial-energy bound, prior-existence assertion, risk conclusion, or minimax-bracket premise. Both endpoints place their constants and thresholds before all extension domains.

The low-smoothness and parametric targets choose their constant after `C`, which contains a fixed extension domain. They prove the displayed fixed-domain brackets and do not separately express a single constant before every extension domain. This is a scope limitation relative to the paper's introductory prose that constants depend only on the numerical model parameters. The main, sharp upper, sharp lower, elementary-upper, and projection-upper endpoints expressly quantify uniformly over domains.

The numbered auxiliary inventory and its exact endpoint scopes are in [COVERAGE.md](COVERAGE.md). A coverage count or a declaration count does not certify every clause of a numbered paper result.

## Statistical model and normalization

The concrete model appears in [Model.lean](../NearlyMinimax/Model.lean) and is repeated in Challenge. `ModelConstants d` requires a positive integer dimension, `s>0`, an integer order satisfying `order<s≤order+1`, `0<p_-<1<p_+`, a positive Hölder radius, `0<v_-<v_+`, and `v_-²<C_4`. The constants are real, hence finite. `ModelConstants.order_eq` proves `order=ceil(s)-1`; `alpha=s-order` belongs to `(0,1]`. Integer smoothness is therefore interpreted as `C^(s-1,1)`, as in the paper.

Covariates are tuples `Fin d → R`. Their law is Lebesgue volume restricted to the closed unit cube and weighted by the unknown density. Admissibility requires measurable density and regression representatives, almost-everywhere density bounds, and density mass one. Errors form a Markov kernel depending on the covariate, with conditional mean zero, the same conditional variance `V` almost everywhere, and conditional fourth moment at most `C_4`. There is no covariate-independent error-law assumption. The observation law is `(X, f(X)+error)` and the sample law is its finite product. The paper explicitly uses the Borel sigma field on its observation domain.

The explicit integrability clauses for powers one, two, and four ensure that the totalized real integral cannot interpret a nonintegrable moment as zero. For probability kernels, a finite fourth moment entails the lower moment integrability. These clauses express the intended finite-moment model.

The regression extends to an arbitrary open domain containing the cube, is continuously differentiable through the specified order there, and obeys the paper's sum/max Hölder norm bound. Each distinct multi-index of total degree at most `order` occurs once in the derivative-supremum sum. The top-order seminorm is a maximum, with explicitly Euclidean distance. [CoordinatePartialBridge.lean](../NearlyMinimax/CoordinatePartialBridge.lean) identifies the sorted coordinate derivative word with iterated Fréchet derivatives on the open domain. [HolderNormConvention.lean](../NearlyMinimax/HolderNormConvention.lean) proves that the pointwise derivative suprema equal the manuscript's essential suprema because these derivatives are continuous on an open set.

Density, regression, and error kernels use ambient representatives. [CubeModelRepresentation.lean](../NearlyMinimax/CubeModelRepresentation.lean) constructs a continuous cube retraction and proves that restricting and extending these representatives leaves observation laws, sample laws, and risks unchanged. It also identifies the ambient worst-case risk with the cube-parameter version. Values outside the design cube have no statistical effect. Torus constructions use `[0,1)` and patch integrals use `[-1,1]^d`; boundaries have zero reference volume.

Risk is an extended nonnegative integral of squared estimator error. Worst-case risk is the supremum over admissible parameters; minimax risk is the infimum over all measurable real-valued estimators; minimax RMS is its square root. [RiskIdentity.lean](../NearlyMinimax/RiskIdentity.lean) identifies this with the infimum of suprema of actual L2 errors without assuming finite estimator second moments. A constant estimator proves finite minimax risk. Thus the `toReal` in the asymptotic targets does not discard an infinite minimax risk. High-smoothness scales are used at `n≥2`; the exact all-n brackets use `n≥1`.

The rates in [Rates.lean](../NearlyMinimax/Rates.lean) and [PaperGoals.lean](../NearlyMinimax/PaperGoals.lean) use RMS normalization throughout:

\[
\lambda=\frac{2(s+1)}{d+4},\qquad
\tau=\log\frac{\sqrt{p_+}+\sqrt{p_-}}{\sqrt{p_+}-\sqrt{p_-}},\qquad
\kappa=4\sqrt{\frac{2\tau(s-1)(d-4s)}{(d+4)^3}},
\]

\[
q_s=\binom{d+\operatorname{order}}d,\qquad
\Gamma=\frac{d(q_s-1/2)}{d+4},\qquad
\Psi_n=n^{-\lambda}e^{-\kappa\sqrt{\log n}}
(\log n)^{(s-1)/(d+4)}.
\]

These are the paper's exact quantities, including the identified `kappa`. The upper scale uses the sum of logarithmic powers; `paperUpperScale_eq` proves it equals `Psi_n(log n)^Gamma` for `n≥2`.

## Proof routes and dependencies

[`paper_main`](../NearlyMinimax/PaperMain.lean) assembles the two proved statistical endpoints. The exponent, polynomial, stretched-exponential, log-expansion, and normalized-risk endpoints then specialize analytic consequences to this bracket. The definitions `MainBracketClaim`, `UpperSharpClaim`, `LowerSharpClaim`, `LowSmoothnessClaim`, and `ParametricClaim` in [PaperGoals.lean](../NearlyMinimax/PaperGoals.lean) are proposition-valued targets. Theorems such as `mainBracketClaim_of_separate_bounds` and `paper_exponent_limit_of_mainBracketClaim` are conditional assembly or analytic infrastructure. Their existence alone would not prove a statistical bound.

The sharp upper route uses observable polynomial/factorial lifts, allocated pilots, and a stabilized pair statistic. Its constructed-pilot theorems discharge moment, localization, bias, and variance hypotheses before the public endpoint. The projection route uses a rectangular monomial basis in place of the paper's total-degree basis. This enlarges a fixed model-dependent feature count and associated constants; it preserves the rate, dimension regime, and Hölder class.

The high-smoothness lower route constructs signed source rows, legal normalized ternary-response paths, marked-history positive priors, nuisance energy estimates, a mass-tilted exceptional tail, and a score-to-risk comparison, followed by rounded saddle allocation. [CompleteSaddleEnergyWitness.lean](../NearlyMinimax/CompleteSaddleEnergyWitness.lean) supplies the spatial-energy witness internally used by the sharp lower proof. [PaperScorePathOriginal.lean](../NearlyMinimax/PaperScorePathOriginal.lean) retains the original variance interval and width penalty in the score-to-risk comparison. The low-smoothness route uses periodic fields and ternary finite-product priors; the parametric lower route uses a legal ternary two-point submodel and Hellinger testing. These routes need not reproduce every informal proof line to prove the stated targets.

The [vendored RoughRegime development](../Vendor/RoughRegime.lean) supplies reusable components, including general testing, polynomial and Cauchy analysis, and squared-integral/L2 identities. Its other model and rate theorems do not replace this paper's minimax risk. Mathlib supplies the underlying analysis, probability, finite-dimensional algebra, and classical library results. Historical comparisons and cited literature remain manuscript context; the selected proof endpoints do not establish every bibliographic statement.

## Material limitations

The high-smoothness bounds leave a factor `(log n)^Gamma`; the exact logarithmic power remains unresolved. The paper and selected formalization provide no useful explicit sample-size threshold or optimized leading constants, and do not establish moderate-sample performance. The model concerns constant conditional variance, the stated strict density and variance/fourth-moment margins, and a Hölder extension of the regression. Other variance models and Hölder conventions require separate arguments.

The low-smoothness and parametric selected statements have the fixed-domain quantifier limitation described above. Generic field-localization lemmas require a countably generated observation sigma algebra; this is automatic for the original standard Borel observation domain. Some numbered auxiliary statements are supported through multiple declarations, and some generic results remain conditional on explicitly supplied hypotheses. See [COVERAGE.md](COVERAGE.md) for those distinctions.

This source review checks mathematical translation and scope. Compilation, transitive-axiom auditing, Comparator, and independent kernel checks validate formal proof terms relative to the concrete definitions. They do not establish human review, certify every semantic translation, or predict submission approval.
