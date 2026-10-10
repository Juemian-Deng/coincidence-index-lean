# Coincidence index and Lean proofs

Private preparation repository. Keep this repository private until the owner explicitly approves publication. No public release, deployment, or license grant is made here.

## Contents and claim boundaries

This repository organizes three previously verified components. Each has its own source directory because some module names overlap; do not combine their object search paths.

| Component | Entry point | Formal scope |
| --- | --- | --- |
| `projects/wang38` | `Wang38.published_conjecture38I`, `Wang38.published_conjecture38II`, `Wang38.published_conjecture38` in `Wang38Full.lean` / `PublishedStatement.lean` | Both published Wang–Wang–Yu Conjecture 38 statements and their conjunction |
| `projects/even_bound` | `WrittenTheoremB.writtenTheoremB` in `WrittenTheoremB.lean` | The rational orthogonal matrix lower bound `n ≤ 2 [ℤⁿ : {x : Rx is integral}]` under evenness of this coincidence subgroup |
| `projects/global_support` | `GlobalSupportBound.rational_global_support_bound` in `GlobalSupportBound.lean` | Literal nonintegral row and column counts agree, and each is at most twice the actual coincidence-subgroup index, for every rational orthogonal matrix |

For the global theorem, rational orthogonality is the only public mathematical hypothesis. Integral coordinate tails and dimension zero are covered. The source contains the definitions and exact hypotheses; the descriptions above are a guide, not replacement theorem statements.

The physical boundary-degeneracy dictionary, attainment in all relevant dimensions, equality/minimizer classifications, general equality/reflection classifications, additive reflection threshold, and graph/covering applications are not claimed as Lean-certified here. This repository does not claim that the entire written paper is formalized. It makes no novelty, priority, or independent-human-review claim.

## Verification status

The recovered 10 October 2026 evidence records a fresh Lean 4.34.1 source rebuild, using Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`:

- Wang38: 42 original source/audit modules; strict endpoint proof-closure audit; supplementary runtime metadata audit. Whole-import `leanchecker --fresh` finished with exit 0.
- Even lower bound: 26 source/audit modules and 2 supplementary auditors.
- Universal support: 34 theorem/regression modules, producer axiom audit, and 2 independent auditors.
- Named endpoints use only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or custom axiom was found in proof sources.

Wang's ordinary structurally recursive `sumN` has a compiler-generated partial runtime helper, `Wang38.Frequency.sumN._unsafe_rec`. It is not in any of the three final endpoint proof closures. An initial supplementary audit that rejected every partial generated declaration failed for that reason; the original diagnostic is retained. The subsequent strict proof-closure audit passed. Do not describe the project as having no partial generated declarations at all.

All 109 packaged Lean files match their dated evidence hashes byte-for-byte. Packaging checks verify those identities, source import order, and the repository hash manifest. The reorganized portable replay wrapper has been syntax/smoke checked; it has not itself been executed with Lean in this packaging environment. Historical Lean success must not be confused with a new run of this wrapper.

The workflow **Frozen source integrity** checks packaging integrity only. A green workflow is not a fresh Lean compilation. The optional global-support whole-import `leanchecker --fresh` replay was not run in the 10 October verification; its own-source and audit rebuilds passed.

## Reproduce

Python 3 is sufficient for the packaging check:

```sh
python3 scripts/verify.py
```

For a new Lean source rebuild, install the official Lean 4.34.1 toolchain, and prepare a clean official Mathlib checkout at the exact commit above, with the exact dependency revisions in `verification/2026-10-10/global_support/environment.json`. Populate its official cache using that checkout's normal `lake exe cache get` workflow. No binaries or caches are vendored here.

Then provide the existing Mathlib directory and directory containing the pinned `lean` and `lake` executables:

```sh
python3 scripts/verify.py --replay --project all \
  --mathlib /absolute/path/to/mathlib4 \
  --lean-bin /absolute/path/to/lean-4.34.1/bin \
  --out /absolute/path/outside-this-repository/new-replay
```

`--project` may instead be `wang38`, `even_bound`, or `global_support`. The output directory must not already exist. The script validates pins and dependency checkouts, isolates each project's object files, rebuilds in recorded order, runs auditors, checks reported axioms, and writes logs and a new receipt. Only audit-output path literals are relocated in temporary copies; frozen repository sources remain unchanged. This command does not perform the additional whole-import `leanchecker` replay.

## Layout

- `projects/`: frozen proof sources and successful audit programs.
- `verification/config.json`: pinned versions, module order, and audit configuration.
- `verification/source_provenance.json`: exact mapping to recovered evidence members.
- `verification/2026-10-10/`: selected historical receipts, logs, provenance, and original evidence manifest.
- `verification/repository_sha256.json`: hashes of packaged files, excluding this manifest itself.
- `scripts/verify.py`: integrity checks and optional isolated source rebuild.

The original evidence manifest describes the larger verification ZIP; large full dependency graphs and unrelated evidence members are intentionally not copied into this repository. Use `repository_sha256.json` to check this repository, not the original evidence manifest as a closed repository listing. Historical receipts retain original execution paths as provenance; they are not paths expected on your machine.

No license has been selected. Dependencies retain their own licenses. Public distribution needs an owner decision.

[中文说明](README.zh-CN.md)
