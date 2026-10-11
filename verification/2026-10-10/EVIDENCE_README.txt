FRESH LEAN VERIFICATION — 10 OCTOBER 2026

This directory records a new source rebuild of three recovered proof packages.
It is not a reproduction of historical log text. The Lean compiler and Mathlib
cache were obtained from official sources and pinned to the recorded versions.
All frozen proof sources and their original archive logs were left unchanged.

Confirmed source-level results
1. Wang38.published_conjecture38I: PASS.
2. Wang38.published_conjecture38II: PASS.
3. Wang38.published_conjecture38: PASS, the conjunction of the two published
   conjecture statements. All 42 original source/audit modules compiled.
4. WrittenTheoremB.writtenTheoremB: PASS, the actual rational orthogonal matrix
   theorem n <= 2 * [Z^n : {x | Rx is integral}] under evenness of this subgroup.
   Its integer and index formulations also passed. The frozen 26 modules and
   two statement/axiom audit helpers compiled in a new output directory.
5. GlobalSupportBound.rational_global_support_bound: PASS, equality of literal
   nonintegral row/column counts and both counts <= twice the actual index.
   All 34 project modules, producer audit, and two independent auditors compiled.

All named endpoints report only propext, Classical.choice and Quot.sound.
Comment-stripped source scans found no sorry, admit, custom axiom, unsafe,
native_decide, implemented_by or extern in the project proof sources.

Wang generated-code nuance
The first supplementary audit imposed the overbroad condition that every
compiler-generated declaration be non-partial. It stopped at
Wang38.Frequency.sumN._unsafe_rec. The original diagnostic is retained.
The logical sumN is a safe definition implemented using Nat.brecOn. Lean also
creates a partial executable helper for ordinary structural recursion; both
sumN and the helper have no axioms. The helper is absent from all three final
endpoint proof-dependency closures. The strict recursive proof-closure audit
passed, with 51,526, 14,885 and 51,778 constants respectively and no missing,
unsafe or partial proof dependency. All 731 local/generated declarations were
scanned for custom axioms; the sole local partial runtime helper is documented.
No theorem source was edited to obtain these results.

Claim boundaries
The even-lattice formalization covers the mathematical lower bound. The
physical boundary-degeneracy dictionary, attainment for all relevant dimensions,
and equality/minimizer classifications remain written arguments. The universal
support formalization does not include the general equality/reflection
classifications or the additive reflection threshold in the current paper.
The independent semantic audit against the original conjectures is a separate
review; compilation alone is not a novelty, priority, or human-review claim.

Trust and extra checks
The official Lean 4.34.1 executable hash matches the historical audit; this is
provenance, not an independently implemented kernel or release-signature check.
The pinned Mathlib tree and eight dependency trees are clean at their exact
recorded revisions. Cached imported objects come from the official cache.
The additional Wang whole-import leanchecker --fresh replay PASSED with exit 0
in 13m4.168s; this rechecks the complete imported kernel environment.
The optional analogous global-support whole-import replay was NOT_REQUESTED;
its own-source proof/auditor rebuild and recursive axiom audit both passed.

See FRESH_ENVIRONMENT_PROVENANCE.json, POST_REPLAY_SOURCE_INTEGRITY.json,
wang_both_replay/FRESH_ENDPOINT_RECEIPT.json,
even_lower_bound_replay/REPLAY_RECEIPT.json and
global_support_replay/REPLAY_RECEIPT.json for exact results and identities.
