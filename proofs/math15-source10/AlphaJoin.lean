import SharedConstructionsSnapshot
import StemInduction

namespace Math15Source10

theorem Complete.good {V E : Type*} {m : ℕ} {f : V → ℕ} {a : E → V × V}
    (h : Complete m f a) : Math15.Labeling.Good m f a :=
  ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩

/-- Join two graceful components at a matching boundary, preserving
surjectivity onto the complete interval of vertex labels. -/
theorem join_complete {V W E F : Type*} {n m k : ℕ}
    {f : V → ℕ} {g : W → ℕ} {a : E → V × V} {b : F → W × W}
    (hf : Complete n f a) (hg : Complete m g b) (ha : Alpha k f a)
    (hk : k≤n) (u : V) (v : W)
    (hmatch : (f u≤k ∧ g v+k=f u+m) ∨ (k<f u ∧ f u=g v+k+1)) :
    Complete (n+m+1) (Math15.Labeling.joinLabel k (m+1) f g)
      (Math15.Labeling.joinEnds u v a b) := by
  have h := Math15.Labeling.join_at_matching_boundary hf.good hg.good ha hk u v hmatch
  refine ⟨h.1,h.2.1,?_,h.2.2.1,h.2.2.2⟩
  intro d hd
  by_cases hlo : d≤k
  · obtain ⟨x,hx⟩ := hf.2.2.1 d (by omega)
    exact ⟨.inl x,by simp [Math15.Labeling.joinLabel,Math15.Labeling.gap,hx,hlo]⟩
  · by_cases hmid : d≤k+m+1
    · obtain ⟨x,hx⟩ := hg.2.2.1 (d-(k+1)) (by omega)
      refine ⟨.inr x,?_⟩
      simp only [Math15.Labeling.joinLabel,hx]
      omega
    · obtain ⟨x,hx⟩ := hf.2.2.1 (d-(m+1)) (by omega)
      refine ⟨.inl x,?_⟩
      simp only [Math15.Labeling.joinLabel,Math15.Labeling.gap,hx]
      split_ifs <;> omega

/-- A center-one graceful component can be joined to S(2,2,s) whenever s!=2.
No upper bound on the small component's alpha index relative to m is needed. -/
theorem join_stem_to_one {W F : Type*} {m : ℕ} {g : W → ℕ} {b : F → W × W}
    (hg : Complete m g b) (v : W) (hv : g v=1) (s : ℕ) (hs : s≠2) :
    ∃ f : Fin (s+5) ⊕ W → ℕ,
      Complete (s+4+m+1) f (Math15.Labeling.joinEnds (stemLeaf s) v (stemEnds s) b) := by
  obtain ⟨k,f,hk,hkn,hf,ha,hr⟩ := onePort_all s hs
  have hm : 1≤m := by have := hg.2.1 v; omega
  have hr' : reverseLabel (s+4) k f (stemLeaf s)=k-1 := by
    simp [reverseLabel,hr,hk]
  refine ⟨_,join_complete (reverse_complete hf ha hkn) (complete_reflect hg)
    (reverse_alpha hf.2.1 ha) hkn (stemLeaf s) v (Or.inl ⟨?_,?_⟩)⟩
  · rw [hr']; omega
  · simp only [hr',hv]; omega

end Math15Source10
#print axioms Math15Source10.join_complete
#print axioms Math15Source10.join_stem_to_one
