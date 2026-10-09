import DoubleSpider

namespace Math15Source10

theorem join_alpha_high {V W E F : Type*} {m k l : ℕ}
    {f : V → ℕ} {g : W → ℕ} {a : E → V × V} {b : F → W × W}
    (ha : Alpha k f a) (hb : Alpha l g b) (hl : l≤m) (u : V) (v : W)
    (hu : k<f u) (hv : g v≤l) :
    Alpha (k+l+1) (Math15.Labeling.joinLabel k (m+1) f g)
      (Math15.Labeling.joinEnds u v a b) := by
  intro e
  cases e with
  | inl e =>
    have := ha e
    simp only [Math15.Labeling.joinEnds,Math15.Labeling.joinLabel,Math15.Labeling.gap]
    split_ifs <;> omega
  | inr e =>
    cases e with
    | none =>
      simp only [Math15.Labeling.joinEnds,Math15.Labeling.joinLabel,Math15.Labeling.gap,
        if_neg (show ¬f u≤k by omega)]
      omega
    | some e =>
      have := hb e
      simp only [Math15.Labeling.joinEnds,Math15.Labeling.joinLabel]
      omega

theorem pathZero_of_marked {n k a b : ℕ} {f : Fin (n+1) → ℕ}
    (hn : n=a+b) (hk : k≤n) (hf : Complete n f (pathEnds n))
    (ha : Alpha k f (pathEnds n)) (hr : ∀v : Fin (n+1),v.val=a → f v=0) : PathZero a b := by
  subst n
  exact ⟨k,f,hk,hf,ha,hr (pathJunction a b) rfl⟩

theorem pathZero_prefix (a b : ℕ) (hb : 2≤b)
    (hsize : a/2≤(b-1)/2) (hexc : a/2=0 ∨ b-1≠4*(a/2)) : PathZero a b := by
  obtain ⟨g,hg,ha,hr⟩ := lowEndpoint_all (b-1) (a/2) hsize hexc
  have hc := prefix_complete a (b-1) g hg (by omega) hr
  have hal := prefix_alpha a (b-1) g hg ha (by omega) hsize hr
  apply pathZero_of_marked (by omega) (by omega) hc hal
  intro v hv
  simp [prefixLabel,concatVertex,hv,Math15.Labeling.joinLabel,Math15.Labeling.gap,walecki]

/-- A complementary alternating block puts zero next to its high endpoint;
joining there avoids the exceptional endpoint value of the first construction. -/
theorem pathZero_neighbor (a b : ℕ) (ha : 1≤a) (hb : 3≤b)
    (hsize : a+1-a/2-1≤(b-2)/2)
    (hexc : b-2≠4*(a+1-a/2-1)) : PathZero a b := by
  obtain ⟨g,hg,hag,hrg⟩ := lowEndpoint_all (b-2) (a+1-a/2-1) hsize (Or.inr hexc)
  let f : Fin (a+1+1) → ℕ := fun v => a+1-walecki (a+1) v
  have hf : Complete (a+1) f (pathEnds (a+1)) := complete_reflect (walecki_complete (a+1))
  have haf : Alpha (a/2) f (pathEnds (a+1)) := by
    have hh := complement_alpha (walecki_complete (a+1)).2.1 (walecki_alpha (a+1)) (by omega)
    convert hh using 1 <;> omega
  have hfr : f 0=a+1 := by simp [f,walecki]
  let F := Math15.Labeling.joinLabel (a/2) (b-2+1) f g ∘ concatVertex (a+1) (b-2)
  have hc : Complete (a+1+(b-2)+1) F (pathEnds (a+1+(b-2)+1)) := by
    apply concat_complete
    apply join_complete hf hg haf (by omega) 0 0
    exact Or.inr ⟨by rw [hfr]; omega,by rw [hfr,hrg]; omega⟩
  have hal : Alpha (a/2+(b-2)/2+1) F (pathEnds (a+1+(b-2)+1)) := by
    exact concat_alpha (join_alpha_high haf hag (by omega) 0 0 (by rw [hfr]; omega) (by rw [hrg]; omega))
  apply pathZero_of_marked (by omega) (by omega) hc hal
  intro v hv
  have hsub : a+1-v.val=1 := by omega
  simp [F,concatVertex,show v.val≤a+1 by omega,hsub,f,walecki,
    Math15.Labeling.joinLabel,Math15.Labeling.gap]

theorem pathZero11 : PathZero 1 1 := by
  refine ⟨0,![2,0,1],by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pathZero35 : PathZero 3 5 := by
  refine ⟨3,![5,1,8,0,6,3,4,2,7],by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pathZero_ordered_unbalanced (a b : ℕ) (ha : 1≤a) (hab : a≤b)
    (hex : a≠b ∨ a%2=1) : PathZero a b := by
  by_cases hb : b=1
  · have haa : a=1 := by omega
    subst a; subst b; exact pathZero11
  · by_cases hp : a/2=0 ∨ b-1≠4*(a/2)
    · exact pathZero_prefix a b (by omega) (by omega) hp
    · by_cases h3 : a=3
      · have h5 : b=5 := by omega
        subst a; subst b; exact pathZero35
      · exact pathZero_neighbor a b ha (by omega) (by omega) (by omega)

theorem model_unbalanced_all {a b c s : ℕ} (ha : 3≤a) (hb : a≤b) (hc : b≤c+1)
    (hex : a≠b ∨ a%2=1) : ModelGraceful a b c s := by
  by_cases hs : s=2
  · subst s
    apply model_of_markzero (pathZero_ordered_unbalanced a b (by omega) hb hex)
    obtain ⟨f,hf,hr⟩ := stem_mark_three_zero (2+c+2) (by omega)
    refine ⟨f,hf,?_⟩
    intro v hv
    have he : v=7 := Fin.ext (by simpa [Nat.mod_eq_of_lt (show 7<2+c+2+5 by omega)] using hv)
    simpa only [he] using hr
  · exact model_one ha hb hc (by omega) hs

end Math15Source10
#print axioms Math15Source10.pathZero_ordered_unbalanced
#print axioms Math15Source10.model_unbalanced_all
