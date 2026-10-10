# Math 15 — Source 5

For a finite set of four positive integer speeds with collective gcd 1 and pairwise gcd at most 2, let `ML` be the maximum, over one circle period, of the minimum distance of a runner from the origin. The theorem proves

- `ML >= 1/4`, or
- `ML = s / (4*s+k)` for natural numbers `s,k` with `1 <= k <= 4` and `k <= s`.

The exact statement is `Math15.LonelyRunner.Target05` in [CanonicalTarget.lean](CanonicalTarget.lean). The final proof is `Bounty.target` in [Main.lean](Main.lean). It combines an unbounded structural reduction with an exhaustive, kernel-evaluated finite certificate. The file includes all auxiliary proof declarations and certificate data.

For a guided explanation with worked examples, development history, and reusable lessons, read [How the four speed spectrum proof works](../../docs/source05-development.md).

## Verification

The original full proof was checked with Lean 4.27.0 / Mathlib v4.27.0. Its transitive axioms were only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom axioms.

This is the selected presentation with 1,187 comment edits. Its non-comment bytes match the original checked payload exactly. The complete published file adds the same local import and namespace wrapper used for checking. **The cleaned complete file has not received a fresh full Lean compilation.** The [evidence record](../../evidence/source05.json) records both original and published hashes; it does not present the old receipt as a new compilation.

To reproduce with Lean installed:

```sh
cd proofs/math15-source05
lake update
lake exe cache get
lake build
```

The full finite certificate is large and compilation is resource intensive. In a workspace with a shared bounded verification launcher, use that launcher and its resource policy.

## Sources

- [Conjectures.io Math 15, Source 5](https://conjectures.io/problems/math15catalog-source05), exact task target.
- [Fan–Sun, arXiv:2306.10417](https://arxiv.org/abs/2306.10417), the amended Lonely Runner spectrum question.
- [Kravitz, arXiv:1912.06034](https://arxiv.org/abs/1912.06034), relevant spectrum and structural results.

These references motivated the work. They are not imported as unproved axioms. This repository makes no priority or reward claim.
