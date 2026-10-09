import BalancedBases
import PathTailTwelve

namespace Math15Source10

theorem nearZeroPort_step (h : ℕ) (hh : 3≤h) (hp : NearZeroPort h) : NearZeroPort (h+6) := by
  obtain ⟨f,hf,ha,h0,h2,hr⟩ := hp
  let F := nearThreeTailLabel (2*h+2) (h+1) f ∘ growPathVertex (2*h+2)
  have hF : Complete (2*h+2+12) F (pathEnds (2*h+2+12)) :=
    growPath_complete (near_three_tail_complete hf ha (by omega) ⟨2*h+2,by omega⟩ hr)
  have hA : Alpha (h+1+6) F (pathEnds (2*h+2+12)) :=
    growPath_alpha (near_three_tail_alpha hf ha (by omega) ⟨2*h+2,by omega⟩ hr)
  have hF0 : F 0=3 := by
    simp only [F,Function.comp_apply]
    rw [show growPathVertex (2*h+2) 0=.inl 0 by simp [growPathVertex]]
    rw [near_three_tail_old hf.2.1 (by omega),h0]
    simp [show 3≤h+1 by omega]
  have hF2 : F 2=0 := by
    simp only [F,Function.comp_apply]
    rw [show growPathVertex (2*h+2) 2=.inl 2 by
      simp [growPathVertex,Fin.ext_iff,Nat.mod_eq_of_lt (show 2<2*h+2+12+1 by omega),show 2≤2*h+2 by omega,
        Nat.mod_eq_of_lt (show 2<2*h+2+1 by omega)]]
    rw [near_three_tail_old hf.2.1 (by omega),h2]
    simp
  have hFr : F ⟨2*h+2+12,by omega⟩+3=h+1+6 := by
    simp only [F,Function.comp_apply]
    rw [show growPathVertex (2*h+2) ⟨2*h+2+12,by omega⟩=.inr 11 by
      simp [growPathVertex,Fin.ext_iff]]
    rw [near_three_tail_last]
  have hn : 2*(h+6)+2=2*h+2+12 := by omega
  have hk : h+6+1=h+1+6 := by omega
  simpa only [NearZeroPort,hn,hk] using
    (show ∃ f : Fin (2*h+2+12+1) → ℕ,
      Complete (2*h+2+12) f (pathEnds (2*h+2+12)) ∧
      Alpha (h+1+6) f (pathEnds (2*h+2+12)) ∧ f 0=3 ∧ f 2=0 ∧
      f ⟨2*h+2+12,by omega⟩+3=h+1+6 from ⟨F,hF,hA,hF0,hF2,hFr⟩)

theorem nearZeroPort_all (h : ℕ) (hh : 3≤h) (h5 : h≠5) : NearZeroPort h := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    by_cases hs : h≤11
    · have he : h=3 ∨ h=4 ∨ h=6 ∨ h=7 ∨ h=8 ∨ h=9 ∨ h=10 ∨ h=11 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact nearZeroPort3
      · exact nearZeroPort4
      · exact nearZeroPort6
      · exact nearZeroPort7
      · exact nearZeroPort8
      · exact nearZeroPort_step 3 (by omega) nearZeroPort3
      · exact nearZeroPort_step 4 (by omega) nearZeroPort4
      · exact nearZeroPort11
    · have hp := nearZeroPort_step (h-6) (by omega) (ih (h-6) (by omega) (by omega) (by omega))
      simpa only [show h-6+6=h by omega] using hp

theorem pathZero_of_nearPort (h : ℕ) (hh : 3≤h) (hp : NearZeroPort h) : PathZero (2*h) (2*h) := by
  obtain ⟨f,hf,ha,h0,h2,hr⟩ := hp
  obtain ⟨g,hg,hag,hg0⟩ := lowEndpoint_all (2*h-3) (h-2) (by omega) (Or.inr (by omega))
  let F := Math15.Labeling.joinLabel (h+1) (2*h-3+1) f (fun v => 2*h-3-g v) ∘
    concatVertex (2*h+2) (2*h-3)
  have hF : Complete (2*h+2+(2*h-3)+1) F (pathEnds (2*h+2+(2*h-3)+1)) := by
    apply concat_complete
    apply join_complete hf (complete_reflect hg) ha (by omega) 0 0
    exact Or.inl ⟨by rw [h0]; omega,by rw [h0,hg0]; omega⟩
  have hA := concat_alpha (join_alpha ha
    (complement_alpha hg.2.1 hag (show (2*h-3)/2<2*h-3 by omega))
    (show 2*h-3-(2*h-3)/2-1≤2*h-3 by omega) (0 : Fin (2*h+2+1)) (0 : Fin (2*h-3+1))
    (by rw [h0]; omega) (by rw [hg0]; omega))
  apply pathZero_of_marked (by omega) (by omega) hF hA
  intro v hv
  have hc : concatVertex (2*h+2) (2*h-3) v=.inl (2 : Fin (2*h+2+1)) := by
    simp [concatVertex,hv,show 2*h≤2*h+2 by omega,Fin.ext_iff,
      Nat.mod_eq_of_lt (show 2<2*h+2+1 by omega)]
  simp only [F,Function.comp_apply,hc,Math15.Labeling.joinLabel,Math15.Labeling.gap,h2]
  simp

theorem pathZero1010 : PathZero 10 10 := by
  refine ⟨10,![4,15,5,17,3,18,2,19,1,20,0,13,8,16,7,14,10,11,9,12,6],by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pathZero_balanced (h : ℕ) (hh : 2≤h) : PathZero (2*h) (2*h) := by
  by_cases h2 : h=2
  · subst h; exact pathZero44
  · by_cases h5 : h=5
    · subst h; exact pathZero1010
    · exact pathZero_of_nearPort h (by omega) (nearZeroPort_all h (by omega) h5)

theorem pathZero_swap {a b : ℕ} (hp : PathZero a b) : PathZero b a := by
  obtain ⟨k,f,hk,hf,ha,hr⟩ := hp
  apply pathZero_of_marked (Nat.add_comm a b) hk (path_reverse_complete hf) (path_reverse_alpha ha)
  intro v hv
  have he : reversePathVertex (a+b) v=pathJunction a b := by
    apply Fin.ext; simp only [reversePathVertex,pathJunction]; omega
  simpa only [Function.comp_apply,he] using hr

/-- Rooted-zero alpha paths, with the precise central-P5 exception. -/
theorem pathZero_all (a b : ℕ) (ha : 1≤a) (hb : 1≤b) (hex : a≠2 ∨ b≠2) : PathZero a b := by
  have ordered (a b : ℕ) (ha : 1≤a) (hab : a≤b) (hex : a≠2 ∨ b≠2) : PathZero a b := by
    by_cases hu : a≠b ∨ a%2=1
    · exact pathZero_ordered_unbalanced a b ha hab hu
    · have he : a=b := by omega
      subst b
      have h := pathZero_balanced (a/2) (by omega)
      simpa only [show 2*(a/2)=a by omega] using h
  by_cases hab : a≤b
  · exact ordered a b ha hab hex
  · exact pathZero_swap (ordered b a hb (by omega) hex.symm)

theorem model_large_all {a b c s : ℕ} (ha : 3≤a) (hb : a≤b) (hc : b≤c+1) :
    ModelGraceful a b c s := by
  by_cases hs : s=2
  · subst s
    apply model_of_markzero (pathZero_all a b (by omega) (by omega) (by omega))
    obtain ⟨f,hf,hr⟩ := stem_mark_three_zero (2+c+2) (by omega)
    refine ⟨f,hf,?_⟩
    intro v hv
    have he : v=7 := Fin.ext (by simpa [Nat.mod_eq_of_lt (show 7<2+c+2+5 by omega)] using hv)
    simpa only [he] using hr
  · by_cases he : a=4 ∧ b=4
    · obtain ⟨rfl,rfl⟩ := he
      exact model44_all c s (by omega)
    · exact model_one ha hb hc (by omega) hs

end Math15Source10
#print axioms Math15Source10.nearZeroPort_all
#print axioms Math15Source10.pathZero_balanced
#print axioms Math15Source10.pathZero_all
#print axioms Math15Source10.model_large_all
