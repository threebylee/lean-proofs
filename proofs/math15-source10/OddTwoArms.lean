import CaterpillarCore

namespace Math15Source10

/-- Cross-edge orientations for the perfect-matching representation of the
tree with three length-two arms on the left, two on the right, and bridge
length 2t+1. Matching pairs along the bridge alternate their orientation. -/
def oddSide (t : ℕ) : CoreE t → Bool
  | .inl i => decide (i.val % 2 = 0)
  | .inr j => if j.val < 3 then false else decide (t % 2 = 0)

def oddEnds (t : ℕ) := pairEnds (coreEnds t) (oddSide t)
def oddLabel (t : ℕ) := pairLabel (t+5) (coreLabel t)

theorem odd_complete (t : ℕ) : Complete (2*t+11) (oddLabel t) (oddEnds t) := by
  convert matching_lift (core_complete t) (oddSide t) using 1 <;>
    simp [oddLabel, oddEnds] <;> omega

end Math15Source10

#print axioms Math15Source10.odd_complete
