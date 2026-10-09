import StemPhysical
import StemInduction

namespace Math15Source10

def NearMark (s j : ℕ) : Prop :=
  ∃ (k : ℕ) (f : Fin (s+5) → ℕ), 1≤k ∧ k<s+4 ∧
    Complete (s+4) f (stemEnds s) ∧ Alpha k f (stemEnds s) ∧
    f (stemLeaf s)+1=k ∧ (∀v : Fin (s+5),v.val=j → f v=0 ∨ f v=s+4)

def MarkZero (s j : ℕ) : Prop :=
  ∃ f : Fin (s+5) → ℕ, Complete (s+4) f (stemEnds s) ∧
    ∀v : Fin (s+5),v.val=j → f v=0

theorem nearMark_step {s j : ℕ} (hj : j<s+5) (h : NearMark s j) : NearMark (s+4) j := by
  obtain ⟨k,f,hk,hkm,hc,ha,hr,hz⟩ := h
  refine ⟨k+2,nearTailLabel (s+4) k f ∘ growFin (s+5),by omega,by omega,?_,?_,?_,?_⟩
  · exact grow_stem_complete s _ (near_tail_complete hc ha (by omega) (stemLeaf s) hr)
  · exact grow_stem_alpha s _ _ (near_tail_alpha hc ha (by omega) (stemLeaf s) hr)
  · simp only [Function.comp_apply,grow_stem_leaf,near_tail_last]
  · intro v hv
    have he : growFin (s+5) v = .inl ⟨j,hj⟩ := by
      simp [growFin,hv,hj]
    simp only [Function.comp_apply,he]
    rw [near_tail_old hc.2.1 (show k≤s+4 by omega)]
    rcases hz ⟨j,hj⟩ rfl with hz | hz
    · left; simp [hz]
    · right; simp [hz,show ¬s+4≤k by omega]

theorem nearMark_zero {s j : ℕ} (hj : j<s+5) (h : NearMark s j) : MarkZero s j := by
  obtain ⟨k,f,hk,hkm,hc,ha,hr,hz⟩ := h
  rcases hz ⟨j,hj⟩ rfl with hz | hz
  · refine ⟨f,hc,?_⟩
    intro v hv
    have he : v=⟨j,hj⟩ := Fin.ext hv
    simpa only [he] using hz
  · refine ⟨fun v => s+4-f v,complete_reflect hc,?_⟩
    intro v hv
    have he : v=⟨j,hj⟩ := Fin.ext hv
    simp [he,hz]

theorem nearMark_1_8 : NearMark 8 5 := by
  refine ⟨6,![6,8,3,7,4,12,0,11,1,10,2,9,5],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearMark_2_8 : NearMark 8 6 := by
  refine ⟨6,![6,8,3,7,4,12,0,11,1,10,2,9,5],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearMark_2_9 : NearMark 9 6 := by
  refine ⟨6,![9,1,11,4,10,2,13,0,12,3,7,6,8,5],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearMark_2_10 : NearMark 10 6 := by
  refine ⟨7,![7,9,3,8,5,12,0,14,1,11,4,13,2,10,6],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearMark_2_11 : NearMark 11 6 := by
  refine ⟨7,![9,4,12,5,11,0,15,1,14,2,13,3,10,7,8,6],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearMark_6_10 : NearMark 10 10 := by
  refine ⟨7,![7,11,3,8,5,9,4,10,1,14,0,12,2,13,6],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearMark_6_11 : NearMark 11 10 := by
  refine ⟨7,![8,5,12,4,10,7,9,1,14,0,15,3,13,2,11,6],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearMark_6_12 : NearMark 12 10 := by
  refine ⟨8,![8,10,3,9,6,13,2,15,1,16,0,12,4,14,5,11,7],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearMark_6_13 : NearMark 13 10 := by
  refine ⟨8,![11,4,15,6,12,2,14,1,16,0,17,3,13,5,9,8,10,7],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearMark_1_14 : NearMark 14 5 := by
  refine ⟨9,![6,14,3,13,4,18,0,17,1,16,2,15,5,11,7,12,9,10,8],by decide,by decide,?_,by unfold Alpha; decide,by decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem markZero_1_6 : MarkZero 6 5 := by
  refine ⟨![10,1,9,3,4,0,6,2,7,5,8],?_,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem markZero_2_6 : MarkZero 6 6 := by
  refine ⟨![1,9,2,4,5,10,0,6,8,3,7],?_,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem markZero_2_7 : MarkZero 7 6 := by
  refine ⟨![1,10,2,8,3,11,0,6,5,9,7,4],?_,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem markZero_1_10 : MarkZero 10 5 := by
  refine ⟨![14,1,13,3,12,0,10,2,9,5,11,6,4,7,8],?_,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nearMark_two_all (s : ℕ) (hs : 8≤s) : NearMark s 6 := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hsmall : s<12
    · interval_cases s <;> first | omega | exact nearMark_2_8 | exact nearMark_2_9 | exact nearMark_2_10 | exact nearMark_2_11
    · have he : s=s-4+4 := by omega
      have hh := nearMark_step (by omega) (ih (s-4) (by omega) (by omega))
      simpa only [← he] using hh

theorem nearMark_six_all (s : ℕ) (hs : 10≤s) : NearMark s 10 := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hsmall : s<14
    · interval_cases s <;> first | omega | exact nearMark_6_10 | exact nearMark_6_11 | exact nearMark_6_12 | exact nearMark_6_13
    · have he : s=s-4+4 := by omega
      have hh := nearMark_step (by omega) (ih (s-4) (by omega) (by omega))
      simpa only [← he] using hh

theorem nearMark_one_even (s : ℕ) (hs : 8≤s) (h10 : s≠10) (heven : s%2=0) : NearMark s 5 := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hsmall : s<16
    · interval_cases s <;> first | omega | exact nearMark_1_8 | exact nearMark_1_14 | exact nearMark_step (by decide) nearMark_1_8
    · have he : s=s-4+4 := by omega
      have hh := nearMark_step (by omega) (ih (s-4) (by omega) (by omega) (by omega) (by omega))
      simpa only [← he] using hh

theorem stem_mark_one_zero (s : ℕ) (hs : 5≤s) : MarkZero s 5 := by
  by_cases ho : s%2=1
  · have he : 2*(s/2)+1=s := by omega
    obtain ⟨f,hf,hr⟩ := stem_odd_mark_one_zero (s/2)
    have hh : MarkZero (2*(s/2)+1) 5 := by
      refine ⟨f,hf,?_⟩
      intro v hv
      have hh : v=5 := Fin.ext (by simpa [Nat.mod_eq_of_lt (show 5<2*(s/2)+1+5 by omega)] using hv)
      simpa only [hh] using hr
    simpa only [he] using hh
  · by_cases h6 : s=6
    · subst s; exact markZero_1_6
    · by_cases h10 : s=10
      · subst s; exact markZero_1_10
      · exact nearMark_zero (by omega) (nearMark_one_even s (by omega) h10 (by omega))

theorem stem_mark_two_zero (s : ℕ) (hs : 6≤s) : MarkZero s 6 := by
  by_cases h8 : 8≤s
  · exact nearMark_zero (by omega) (nearMark_two_all s h8)
  · have he : s=6 ∨ s=7 := by omega
    rcases he with rfl | rfl
    · exact markZero_2_6
    · exact markZero_2_7

theorem stem_mark_six_zero (s : ℕ) (hs : 10≤s) : MarkZero s 10 :=
  nearMark_zero (by omega) (nearMark_six_all s hs)

end Math15Source10
#print axioms Math15Source10.stem_mark_one_zero
#print axioms Math15Source10.stem_mark_two_zero
#print axioms Math15Source10.stem_mark_six_zero
