# Lessons for future proof work

The [four-speed spectrum proof](source05-development.md) and the [graceful tree proof](source10-development.md) solve different kinds of problems. One reduces an unbounded arithmetic question to a finite certificate; the other constructs labelings for arbitrary path lengths and transfers them to every graph in the target family. Their reusable value lies in the specific arguments that made those reductions and constructions work.

The following lessons are suggestions for future research. They do not establish that either proof method solves a new conjecture. Each transfer needs its own mathematical statement and verification.

## Start from what would actually suffice

Source 5 initially pursued a tidy classification of all quartets with small maximum distance. The quartet $\lbrace 1,3,4,14 \rbrace$ refuted that proposed classification while still satisfying the desired spectrum theorem. The successful assembly only needed “the desired conclusion holds, or the speed sum is at most 444.”

Source 10 initially asked too much of a path labeling at a selected vertex. The successful construction allowed different attachment labels and supplied separate cases.

For a new problem, write down the exact conclusion needed by the next step. Then compare it with the current auxiliary claim. A stronger statement is useful when it enables composition or reuse, but it can also introduce a false or unnecessary obligation.

## Track one witness through the entire argument

In Source 5, four runners must be far from the origin at one time. Four independently good times do not suffice. The compressed certificate therefore retains which single time supports all four speeds.

In Source 10, a join requires an equation about the labels of the actual vertices being attached. An appropriate label elsewhere in the component does not solve the attachment problem.

When combining two results, spell out the shared data: the same object, time, vertex, basis, population, or parameter choice. Check whether the first theorem provides those data in the form required by the second. This is often where an apparently complete proof hides a gap.

## Ask finite computation a precise question

The most informative experiments here had sharply limited conclusions. A quartet disproved a proposed classification. A path obstruction disproved a prescribed-label construction. Small labeling certificates suggested reusable extensions. These outcomes narrowed or changed the mathematics.

Before a search, state what success and failure would establish. A witness proves existence for its input. A complete exhaustion can prove nonexistence within its stated finite domain. A timeout proves neither. Finding no counterexample below a cutoff establishes a universal theorem only when a separate argument reduces every case still needing proof to that region.

Source 5's final finite closure required both sound certificates and exhaustive coverage. Source 10's unbounded stem families required both base certificates and an extension theorem. These are different ways to make finite evidence participate in a universal proof.

## Preserve the information needed for the next step

The four-edge extension for graceful trees preserves an endpoint labeled 1. That label is not decorative; it makes the extension repeatable. The full certificate also preserves uniqueness and completeness of edge differences.

The lattice argument preserves the actual speed vector while changing coordinates and constructing relations. Bounds referring to a different lattice or speed set would not complete the argument.

A productive question is: “What information will the next operation need, and does the present lemma preserve it?” The answer should be a mathematical condition with a proof, not an informal promise of compatibility.

## Prefer a sufficient estimate when it closes the proof

Source 5 did not need every available improvement to its numerical bounds. Once the finite theorem covered sum 444, bounds of 437 and 429 were sufficient for their branches.

The tree proof did not need a direct reverse-adjacency proof after obtaining a spanning vertex bijection, edge inclusion, and equality of edge counts. Those established facts already forced graph equality.

Before investing in a sharper estimate or a more elaborate correspondence, try assembling the strongest results already available into the exact target. The missing obligation may be smaller than the one currently under investigation.

## Keep counterexamples attached to the claim they refute

| Saved obstruction | What it rules out | What it does not rule out |
| --- | --- | --- |
| $\lbrace 1,3,4,14 \rbrace$ with $\operatorname{ML}=4/17$ | The proposed positive two-family classification of every low quartet | The Source 5 spectrum conclusion |
| The eight-edge path with its middle vertex required to have alpha label 1 | That particular prescribed-label construction | Ordinary gracefulness of the path or Source 10 |
| The $(1,2,2)$ arm configuration under a shortest-arm selection rule | That selection rule as sufficient for the short-arm assembly | A suitable permutation of the same arms |

Keeping the exact hypotheses with each obstruction prevents both repeating a false shortcut and wrongly abandoning a broader method that still works.

## Separate construction from coverage and transfer

Both proofs have three distinct responsibilities:

| Responsibility | Source 5 | Source 10 |
| --- | --- | --- |
| Produce a valid mathematical object | A common-time witness or a proved spectrum family | A complete labeling certificate |
| Cover every permitted input | Unbounded reduction plus exhaustive finite coverage | Tree decomposition plus exhaustive arm cases |
| Reach the canonical target | Coordinate-to-finite-set transfer and final disjunction | Vertex bijection, edge identification, validator binding |

An impressive construction can still leave the second or third responsibility open. Conversely, a conditional assembly can be valuable before its premises have all been supplied, provided it is labeled as conditional.

## Preserve the difference between explanation and verification

These guides explain existing mathematical arguments; the Lean declarations and matching verification records carry the formal proof claims. A polished explanation does not certify a new theorem. A successful check of one file also does not establish that a later edited file was checked.

The repository makes that distinction explicit for Source 5: the original full proof was checked, while the selected comment cleanup has not had a fresh full compilation. Source 10's published version was freshly checked. That provenance is useful when returning to the work months later.

For a new result, preserve its exact statement, useful hypotheses, proof source, environment, and verification evidence. For a failed attempt, preserve the precise counterexample or unresolved inference. A future reader should be able to tell what can safely be reused without reconstructing the entire project.

## A short reading exercise for the next problem

Choose the guide closest to the structure of the new problem and answer these questions in mathematical terms:

1. What exact conclusion is needed, and which stronger assumptions came from our chosen method?
2. What must remain the same when combining the available lemmas?
3. Which saved obstruction would be the cheapest serious test of the proposed transfer?
4. What proves coverage beyond the examples we can inspect?
5. Which final step connects the construction to the original statement?

Then attempt that transfer or test. The purpose of the questions is to produce a useful derivation, counterexample, or exact remaining obligation.
