import PathEndpoint
import StemTwo

namespace Math15Source10

/-- An endpoint-flexible path attached to the middle of an eight-edge
Walecki path gives center label two for every S(4,4,c+1), c>=2. -/
theorem spider44_center_two (c : ℕ) (hc : 2≤c) :
    ∃ f : Fin 9 ⊕ Fin (c+1) → ℕ,
      Complete (8+c+1) f (spiderEnds 4 4 c) ∧ f (.inl (pathJunction 4 4))=2 := by
  obtain ⟨g,hg,hrg⟩ := path_endpoint_flexible c (c-2) (by omega)
  refine ⟨_,join_complete (walecki_complete 8) hg (walecki_alpha 8) (by omega)
    (pathJunction 4 4) 0 (Or.inl ⟨by decide,?_⟩),?_⟩
  · simp only [hrg]; change c-2+4=2+c; omega
  · simp [Math15.Labeling.joinLabel,Math15.Labeling.gap,walecki,pathJunction]

/-- The two-port counterpart of join_stem_to_one. -/
theorem join_stem_to_two {W F : Type*} {m : ℕ} {g : W → ℕ} {b : F → W × W}
    (hg : Complete m g b) (v : W) (hv : g v=2) (s : ℕ) (hs : 3≤s) (h5 : s≠5) :
    ∃ f : Fin (s+5) ⊕ W → ℕ,
      Complete (s+4+m+1) f (Math15.Labeling.joinEnds (stemLeaf s) v (stemEnds s) b) := by
  obtain ⟨k,f,hk,hkn,hf,ha,hr⟩ := twoPort_all s hs h5
  have hm : 2≤m := by have := hg.2.1 v; omega
  have hr' : reverseLabel (s+4) k f (stemLeaf s)=k-2 := by
    simp [reverseLabel,hr,hk]
  refine ⟨_,join_complete (reverse_complete hf ha hkn) (complete_reflect hg)
    (reverse_alpha hf.2.1 ha) hkn (stemLeaf s) v (Or.inl ⟨?_,?_⟩)⟩
  · rw [hr']; omega
  · simp only [hr',hv]; omega

end Math15Source10
#print axioms Math15Source10.spider44_center_two
#print axioms Math15Source10.join_stem_to_two
