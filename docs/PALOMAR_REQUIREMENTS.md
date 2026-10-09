# Palomar requirements snapshot

The source package targets Palomar's requirements checked on 8 October 2026
(America/New_York; 9 October UTC). The check used the complete primary sources
at these immutable revisions:

| Source | Revision |
| --- | --- |
| [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/tree/96b034cc31a72a63d4f4041911dce337a85c9a04) | `96b034cc31a72a63d4f4041911dce337a85c9a04` |
| [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44) | `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` |
| [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406) | `2891de4c48955af824969a263d31b25e7a9a1406` |
| [Community formalization.yaml schema](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e) | `99c678e569c7c4c0772db297c5ddd5e4c9b6322e` |

The policy is an eligibility and fidelity standard, while the submission
implementation defines the mechanical checks. A successful local check does
not establish Palomar registration, editorial acceptance, or human review.

## Requirements relevant to this package

- The minimum released or release-candidate toolchain is
  `leanprover/lean4:v4.35.0-rc2`. Canonical Mathlib's resolved revision must use
  the same toolchain, including patch and release-candidate suffix.
- Every submitted `.lean` source must use the module system and have at most
  10,000 physical lines. `lakefile.lean` alone is exempt from the header rule.
  The scan includes unused sources and vendored/local path sources and excludes
  generated `.lake` and Git internals. Lean source symlinks are rejected.
- Challenge has hard limits of 1,000 physical lines and 100 KiB; above 300
  lines or 32 KiB, the verifier emits a readability warning.
- Challenge's transitive imports are restricted to Lean core and authenticated
  canonical Mathlib, Tau Ceti, or CSLib with their exact pinned manifest
  closures. Project-specific statement imports are forbidden. This Challenge
  imports Mathlib and defines its statistical model concretely.
- Challenge and Solution are distinct modules. Comparator compares the
  declarations listed in `comparator.json` and the ordinary declaration
  dependencies of their types. Empty `definition_names` means the statistical
  definitions are concrete rather than unspecified definition targets.
- Deliberate theorem placeholders are permitted in Challenge. The selected
  Solution proofs must transitively use only `propext`, `Quot.sound`, and
  `Classical.choice`, without `sorryAx`, `Lean.ofReduceBool`, custom axioms, or
  missing definitions.
- The Lake manifest records every Git dependency by a credential-free public
  GitHub URL and an exact lowercase 40-character commit. The submitted source
  must contain no submodules, Git LFS pointers, or compiled artifacts outside
  `.lake`.
- The submitted source snapshot is limited to 500 MiB. Lake configuration,
  Comparator configuration, and the root license are each limited to 1 MiB;
  `formalization.yaml` is limited to 256 KiB.
- Metadata uses `version: v0.4`, a nonempty project description, human authors
  and responsible maintainers, source provenance, official subject
  classifications, material automation disclosures, and an accurate
  pre-submission review status. Duplicate YAML keys and merge keys are
  rejected. Source authorship and maintainer responsibility do not establish
  review.
- Exactly one conventional root license must mechanically match one standard
  SPDX identifier and `project.license`. MIT is allowed. License detection
  identifies the supplied terms; it does not establish ownership or
  redistribution rights.

## Comparator and independent kernels

The current submission implementation and template judge with the submitted
Lean toolchain's bundled `lake`, `leanexport`, `leanchecker`, `nanoda_bin`,
and `con-ron`. The protected configuration registers NanoDa and con-ron as
independent external kernels; con-ron receives `--jobs=2` in the registry.
`external_kernels` is a verifier-owned field and is absent from the checked-in
configuration. The compatibility field `enable_nanoda` is non-authoritative.
The local verification script creates a temporary protected copy to request
both independent kernels alongside Lean's kernel.

The Policy snapshot still describes older fixed Comparator/NanoDa tool pins
and only NanoDa replay. The current executable verifier, its README, its
[declaration-closure note](https://github.com/PalomarRegistry/PalomarSubmission/blob/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44/docs/comparator-declaration-closure.md),
and the Template agree on the bundled tools and both independent kernels.
The local checks follow that executable implementation. The registry additionally
isolates and exports its canonical Challenge independently of the candidate
Lake build; local Comparator execution does not claim to have run that full
registry sandbox workflow.

The project preflight script imports the pinned official validation functions
from separate tool checkouts and checks the pinned community schema. It also
walks the complete Challenge import closure with Lean's header parser and
checks imported source content against the authenticated dependency blobs.
Verification results must be read together with the exact source revision and
limitations in the verification record.
