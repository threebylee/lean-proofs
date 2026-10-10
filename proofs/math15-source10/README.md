# Math 15 — Sources 10 and 12

For a guided explanation of the constructions, failed shortcuts, and final assembly, read [How the graceful tree proof works](../../docs/source10-development.md).

**Source 10:** every finite tree with exactly two branching vertices, of degrees 4 and 3, admits a graceful labeling. Every other vertex has degree at most 2; all arm lengths are allowed.

A graceful labeling assigns distinct integers from `0` through the number of edges to the vertices so that the absolute differences on edges are exactly `1, 2, ..., |E|`, each once.

**Source 12:** the special case with two terminal arms of length 2 at the degree-3 vertex. It follows immediately from Source 10.

## Proof entry points

- [Main.lean](Main.lean) states both complete results using the original target definitions.
- [CanonicalClosure.lean](CanonicalClosure.lean) assembles the Source 10 proof and its Source 12 corollary.
- [OriginalValidator.lean](OriginalValidator.lean) preserves the original task definitions with only their namespace renamed.
- [ValidatorBinding.lean](ValidatorBinding.lean) checks the final proofs against those definitions.
- [AxiomAudit.lean](AxiomAudit.lean) requests the transitive axioms of every named declaration in the included modules.

The proof decomposes each tree into six paths, chooses a permitted ordering of the arms, applies complete regular and exceptional labeling constructions, and transfers the labeling through a vertex bijection. Edge inclusion becomes equality because both trees have one fewer edge than vertices. No extra decomposition hypothesis remains in the final theorem.

Some helper modules retain conditional presentation lemmas. Their assumptions are explicit, and the final proof constructs its own presentation rather than assuming those lemmas' structural premises.

## Reproduce the check

```sh
cd proofs/math15-source10
lake update
lake exe cache get
lake build
cd ../..
python3 tools/check.py math15-source10
```

The checker rebuilds the publication modules, binds imported sources and objects, and rejects transitive axioms outside `propext`, `Classical.choice`, and `Quot.sound`. In the Conjectures workspace, invoke it through the shared bounded launcher.

The project pins Lean 4.27.0 and Mathlib commit `a3a10db0e9d66acbebf76c5e6a135066525ac900` (v4.27.0). The publication receipt is [source10.json](../../evidence/source10.json); [source10-presentation.json](../../evidence/source10-presentation.json) records the comment-only edits to the original proof modules.

## Provenance

The exact targets are [Math 15 Source 10](https://conjectures.io/problems/math15catalog-source10) and [Source 12](https://conjectures.io/problems/math15catalog-source12). The saved validator's `Math15/Graceful.lean` definitions have SHA-256 `eced473878c1c47d80ced267f9ebcfb9ba0f8fa1fcb7f80be0a5ddd29e42309c` before the namespace-only rename.

The constructions were developed with AI assistance during the Math 15 work. Shared labeling constructions were retained from that work and checked as part of this proof. Publication makes no claim of first discovery, first formalization, or bounty eligibility.
