import PathBlocks
namespace Math15Source10
def PathOne (a b : ℕ) : Prop := ∃ f : Fin (a+b+1) → ℕ,
  Complete (a+b) f (pathEnds (a+b)) ∧ Alpha (a/2+b/2) f (pathEnds (a+b)) ∧
  f (pathJunction a b)=1

theorem pathOne_4_5 : PathOne 4 5 := by
  refine ⟨![3,7,0,9,1,6,4,5,2,8],?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pathOne_4_6 : PathOne 4 6 := by
  refine ⟨![3,10,0,9,1,6,5,7,4,8,2],?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pathOne_4_7 : PathOne 4 7 := by
  refine ⟨![3,11,0,10,1,8,2,7,4,6,5,9],?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pathOne_4_8 : PathOne 4 8 := by
  refine ⟨![4,12,0,11,1,10,3,9,5,8,6,7,2],?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pathOne_4_15 : PathOne 4 15 := by
  refine ⟨![3,19,0,18,1,16,2,15,5,17,6,14,7,12,8,11,9,10,4,13],?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pathOne_5_5 : PathOne 5 5 := by
  refine ⟨![9,0,10,2,7,1,8,4,5,3,6],?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pathOne_6_9 : PathOne 6 9 := by
  refine ⟨![2,15,0,14,4,13,1,12,5,11,3,8,7,9,6,10],?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pathOne_7_9 : PathOne 7 9 := by
  refine ⟨![15,0,16,2,12,3,14,1,13,5,10,4,11,7,8,6,9],?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Math15Source10
#print axioms Math15Source10.pathOne_4_5
#print axioms Math15Source10.pathOne_4_6
#print axioms Math15Source10.pathOne_4_7
#print axioms Math15Source10.pathOne_4_8
#print axioms Math15Source10.pathOne_4_15
#print axioms Math15Source10.pathOne_5_5
#print axioms Math15Source10.pathOne_6_9
#print axioms Math15Source10.pathOne_7_9
