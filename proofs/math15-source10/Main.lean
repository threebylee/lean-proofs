import ValidatorBinding

/-!
Graceful labeling of finite trees with one degree-4 junction and one degree-3
junction. The statement uses the original task definitions; every other
vertex has degree at most two. Source 12 is the immediate special case with
two length-two terminal arms at the degree-3 junction.
-/

namespace LeanProofs.Math15

/-- The full Source 10 target, with no extra structural assumption. -/
theorem source10 : Math15Source10.OriginalValidator.Target10 :=
  Math15Source10.source10_exact_validator

/-- Source 12 follows by restricting Source 10 to its prescribed arm lengths. -/
theorem source12 : Math15Source10.OriginalValidator.Target12 :=
  Math15Source10.source12_exact_validator

end LeanProofs.Math15
