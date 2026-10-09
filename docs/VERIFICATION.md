# Verification record

All required **local mechanical checks passed** for proof revision
`88fdec862ee895fd9f32aee4ed33fa295c6b5a19` using Lean `v4.35.0-rc2` and
Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The content-addressed input digest is
`5ce07cc565f852c56589b6e9cdb1e70b30e5a4a3e3488b26a5a557c02decffca`.

[verification.json](verification.json) records the outcomes and exact binary
hashes. [verification-inputs.json](verification-inputs.json) lists all
663 checked input hashes. It covers every submitted Lean source,
build and dependency pins, metadata, license and notice, verification scripts,
original-source baseline, and manuscript sources. Derived documentation,
reports and the PDF are outside that proof-input digest. The later documentation
commit changes no verified proof input. Raw transcripts and tool caches are
kept outside the public source tree.

## Completed checks

| Check | Result |
| --- | --- |
| Original mathematical source preservation | All 642 bodies recovered byte-for-byte after removing only the documented module/import/exposure additions |
| Source compilation | All 645 submitted Lean sources checked; library, Challenge and Solution built, and Audit compiled and executed |
| Transitive axiom inventory | 643 proof modules, 10,858 declarations and 8,839 theorems; only `propext`, `Classical.choice`, `Quot.sound` |
| Private implementation coverage | 2,100 private/generated declarations, including all 64 explicit source-private declarations |
| Selected Solution proofs | All five have exactly the three permitted transitive axioms and no proof holes |
| Comparator | Exact selected statements and their concrete definition closure accepted; no definition holes |
| Independent exported-proof replay | con-ron (`--jobs=2`), NanoDa and Lean's `leanchecker` all accepted; Comparator exited with code 0 |
| Numbered endpoint binding | All 145 references to 133 distinct endpoint theorems resolve in the audited theorem inventory |
| Metadata and licensing checks | Official pinned metadata validator, community v0.4 schema and pinned licensee 10.0.0 MIT detection passed |
| Repository and dependency checks | Nine exact Git pins, matching canonical Mathlib toolchain, source headers, artifact exclusions and current size limits passed |
| Challenge imports | 10,764 transitive source files authenticated; no untrusted imports |
| Paper | Authoritative manuscript compiled with `latexmk -pdf` |
| Input stability | Checked inputs unchanged throughout the complete run |

Challenge has 272 physical lines and 12,159 bytes, within both preferred
readability limits. The largest submitted Lean source has 1,213 lines,
below the 10,000-line limit. The axiom audit uses explicit private imports
under the new module system so private implementation declarations are included.
Challenge's five intentional theorem placeholders are excluded from the proof
inventory; its definitions contain no placeholders. Deprecation and unused
argument warnings remain in the compiler output.

The five `PaperGoals` proposition-valued targets define assertions; they are
not themselves proofs. Their corresponding endpoint theorems and the five
Solution declarations are checked separately. The numbered endpoint check
establishes their existence and allowed axiom dependencies, while the
[coverage review](COVERAGE.md) compares their exact target and scope to the
paper. It does not certify literal equivalence of every clause in all 32
numbered blocks.

## Limits of the result

The [fidelity review](FIDELITY.md) is automated. Kernel acceptance establishes
formal proof validity for the encoded statements; it does not establish human
mathematical review or informal-source equivalence. The low-smoothness and
parametric constants are chosen after a fixed extension domain. Some auxiliary
lemmas are conditional infrastructure or components, and some constructions
follow alternative routes. The refined bracket retains a logarithmic gap;
optimized constants, explicit useful thresholds and moderate-sample performance
are not proved.

No local mechanical blocker remains. Palomar's hosted independent canonical
Challenge export, editorial review, publication, submission and registration
have not run. The requirements snapshot and executable-tooling distinctions
are in [PALOMAR_REQUIREMENTS.md](PALOMAR_REQUIREMENTS.md). License detection
identifies MIT text and does not establish manuscript redistribution rights;
[NOTICE](../NOTICE) records that separate boundary.

Run `python3 scripts/verify.py --work-dir ../verification-run --paper` from the
repository root to reproduce the complete checks with the prerequisites in
[README.md](../README.md). Run `python3 scripts/snapshot.py` to compare the
current proof-input digest before relying on this record.
