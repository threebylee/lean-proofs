import PathAlphaIndex

namespace Math15Source10

/-- Attach an arbitrary path at a zero-labeled root. Its other endpoint can
be made zero, irrespective of the base tree's alpha-labeling status. -/
theorem rooted_leaf_extension {V E : Type*} [DecidableEq V] {m : ℕ}
    {f : V → ℕ} {ends : E → V × V} (hf : Complete m f ends)
    (r : V) (hr : f r=0) (p : ℕ) :
    ∃ F : Fin (p+1) ⊕ {v : V // v≠r} → ℕ,
      Complete (p+m) F (wedgeEnds (0 : Fin (p+1)) r (pathEnds p) ends) ∧
      F (.inl ⟨p,by omega⟩)=0 := by
  let g := reverseLabel p (p/2) (walecki p)
  have hg := reverse_complete (walecki_complete p) (walecki_alpha p) (show p/2≤p by omega)
  have hga := reverse_alpha (walecki_complete p).2.1 (walecki_alpha p)
  have hg0 : g 0=p/2 := by simp [g,reverseLabel,walecki]
  let F := wedgeLabel (v:=r) (p/2) m g f
  have hF : Complete (p+m) F (wedgeEnds (0 : Fin (p+1)) r (pathEnds p) ends) :=
    wedge_complete hg hf hga (by omega) 0 r hg0 hr
  by_cases he : p%2=0
  · refine ⟨F,hF,?_⟩
    simp [F,wedgeLabel,g,reverseLabel,walecki,he,Math15.Labeling.gap]
  · refine ⟨fun v => p+m-F v,complete_reflect hF,?_⟩
    simp only [F,wedgeLabel,g,reverseLabel,walecki,if_neg he,Math15.Labeling.gap]
    split_ifs <;> omega

theorem spider_center_zero_regular (a b c : ℕ) (ha : 1≤a) (hb : 1≤b)
    (hex : a≠2 ∨ b≠2) (hk : a/2+b/2≤c) :
    ∃ f : Fin (a+b+1) ⊕ Fin (c+1) → ℕ,
      Complete (a+b+c+1) f (spiderEnds a b c) ∧ f (.inl (pathJunction a b))=0 := by
  obtain ⟨f,hf,hal,hr⟩ := path_zero_fixed a b ha hb hex
  obtain ⟨g,hg,hg0⟩ := path_endpoint_flexible c (c-(a/2+b/2)) (by omega)
  refine ⟨_,join_complete hf hg hal (by omega) (pathJunction a b) 0 (Or.inl ⟨by rw [hr]; omega,by rw [hr,hg0]; omega⟩),?_⟩
  simp [Math15.Labeling.joinLabel,Math15.Labeling.gap,hr]

end Math15Source10
#print axioms Math15Source10.rooted_leaf_extension
#print axioms Math15Source10.spider_center_zero_regular
