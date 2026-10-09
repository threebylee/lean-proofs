import AlphaTailThree
import PathZero
namespace Math15Source10
def NearZeroPort (h : ℕ) : Prop := ∃ f : Fin (2*h+2+1) → ℕ,
  Complete (2*h+2) f (pathEnds (2*h+2)) ∧ Alpha (h+1) f (pathEnds (2*h+2)) ∧
  f 0=3 ∧ f 2=0 ∧ f ⟨2*h+2,by omega⟩+3=h+1

theorem nearZeroPort3 : NearZeroPort 3 := by
  refine ⟨![3,7,0,8,2,5,4,6,1],?_,by unfold Alpha; decide,by decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearZeroPort4 : NearZeroPort 4 := by
  refine ⟨![3,7,0,10,1,9,4,6,5,8,2],?_,by unfold Alpha; decide,by decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearZeroPort6 : NearZeroPort 6 := by
  refine ⟨![3,10,0,14,1,13,2,11,5,9,6,8,7,12,4],?_,by unfold Alpha; decide,by decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearZeroPort7 : NearZeroPort 7 := by
  refine ⟨![3,11,0,16,1,15,2,14,4,13,8,9,7,10,6,12,5],?_,by unfold Alpha; decide,by decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearZeroPort8 : NearZeroPort 8 := by
  refine ⟨![3,13,0,18,1,17,2,16,4,15,9,10,8,11,7,12,5,14,6],?_,by unfold Alpha; decide,by decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearZeroPort11 : NearZeroPort 11 := by
  refine ⟨![3,19,0,24,1,23,2,22,4,21,7,13,12,14,11,15,10,17,8,16,6,18,5,20,9],?_,by unfold Alpha; decide,by decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Math15Source10
#print axioms Math15Source10.nearZeroPort3
#print axioms Math15Source10.nearZeroPort4
#print axioms Math15Source10.nearZeroPort6
#print axioms Math15Source10.nearZeroPort7
#print axioms Math15Source10.nearZeroPort8
#print axioms Math15Source10.nearZeroPort11
