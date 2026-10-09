import Stem

namespace Math15Source10

def OnePort (s : ℕ) : Prop :=
  ∃ (k : ℕ) (f : Fin (s+5) → ℕ), 1≤k ∧ k≤s+4 ∧
    Complete (s+4) f (stemEnds s) ∧ Alpha k f (stemEnds s) ∧ f (stemLeaf s)=1

def NearPort (s : ℕ) : Prop :=
  ∃ (k : ℕ) (f : Fin (s+5) → ℕ), 1≤k ∧ k<s+4 ∧
    Complete (s+4) f (stemEnds s) ∧ Alpha k f (stemEnds s) ∧
    f (stemLeaf s)+1=k ∧ (f 7=0 ∨ f 7=s+4)

theorem onePort0 : OnePort 0 := by
  refine ⟨2,![1,3,2,4,0],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem onePort1 : OnePort 1 := by
  refine ⟨2,![4,2,3,0,5,1],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem onePort3 : OnePort 3 := by
  refine ⟨3,![5,3,4,2,6,0,7,1],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem onePort6 : OnePort 6 := by
  refine ⟨5,![4,6,5,7,3,9,2,8,0,10,1],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearPort7 : NearPort 7 := by
  refine ⟨5,![6,1,9,5,7,3,10,0,11,2,8,4],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearPort8 : NearPort 8 := by
  refine ⟨6,![4,11,2,8,3,10,0,12,1,9,6,7,5],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearPort9 : NearPort 9 := by
  refine ⟨6,![9,1,11,4,10,2,13,0,12,3,7,6,8,5],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearPort10 : NearPort 10 := by
  refine ⟨7,![7,9,3,8,5,12,0,14,1,11,4,13,2,10,6],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem markZero6 : ∃ f : Fin 11 → ℕ, Complete 10 f (stemEnds 6) ∧ f 7=0 := by
  refine ⟨![6,3,7,4,5,1,10,0,8,2,9],?_,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Math15Source10
#print axioms Math15Source10.onePort0
#print axioms Math15Source10.onePort1
#print axioms Math15Source10.onePort3
#print axioms Math15Source10.onePort6
#print axioms Math15Source10.nearPort7
#print axioms Math15Source10.nearPort8
#print axioms Math15Source10.nearPort9
#print axioms Math15Source10.nearPort10
#print axioms Math15Source10.markZero6
