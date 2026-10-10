# Lean proofs

Formal proofs developed with AI assistance and maintained by [threebylee](https://github.com/threebylee).
This repository preserves the arguments and verification evidence without claiming priority over other solutions.

| Problem | Proof | Verification |
| --- | --- | --- |
| Math 15, Source 5: four-speed amended Lonely Runner spectrum | [Source and instructions](proofs/math15-source05/) | Original exact target checked in Lean 4.27.0; published comment cleanup reviewed, fresh compilation pending |
| Math 15, Source 10: graceful trees with branching degrees 4 and 3; includes Source 12 | [Source and instructions](proofs/math15-source10/) | Published sources freshly checked in Lean 4.27.0; all 607 transitive axiom audits passed |

Each proof directory is an independent Lake project pinned to Lean 4.27.0 and Mathlib v4.27.0.
Verification records in [evidence](evidence/) distinguish checked source bytes from later presentation edits.
Website verification, acceptance, and rewards are separate from these local checks.

## Learning from the proofs

The companion guides explain the mathematics, selected failed approaches, and the changes that led to the final proofs. They include worked examples and links to the relevant Lean declarations.

- [How the four speed spectrum proof works](docs/source05-development.md)
- [How the graceful tree proof works](docs/source10-development.md)
- [Lessons for future proof work](docs/proof-work-lessons.md)

See [NOTICE](NOTICE) for provenance and attribution. Distributed under the Apache License 2.0.
