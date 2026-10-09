import PathEndpoint
import PathOneBases

namespace Math15Source10

theorem pathOne_of_marked {n k a b : ℕ} {f : Fin (n+1) → ℕ}
    (hn : n=a+b) (hk : k=a/2+b/2) (hf : Complete n f (pathEnds n))
    (ha : Alpha k f (pathEnds n)) (hr : ∀v : Fin (n+1),v.val=a → f v=1) : PathOne a b := by
  subst n; subst k
  exact ⟨f,hf,ha,hr (pathJunction a b) rfl⟩

theorem concat_junction (r m : ℕ) :
    concatVertex r m (⟨r,by omega⟩ : Fin (r+m+1+1)) = .inl 0 := by
  simp [concatVertex]

theorem prefix_mark_two (r m : ℕ) (g : Fin (m+1) → ℕ) (hr : 2≤r) :
    prefixLabel r m g (⟨r-2,by omega⟩ : Fin (r+m+1+1))=1 := by
  simp [prefixLabel,concatVertex,show r-2≤r by omega,show r-(r-2)=2 by omega,
    Math15.Labeling.joinLabel,Math15.Labeling.gap,walecki,show 1≤r/2 by omega]

/-- Join two alpha paths at a vertex already labeled one. -/
theorem pathOne_join (a b : ℕ) (ha : 3≤a) (hab : a≤b)
    (ha4 : a≠4) (hexc : b+3≠4*(a/2)) : PathOne a b := by
  obtain ⟨f,hf,haf,hrf⟩ := lowEndpoint_all a 1 (by omega) (Or.inr (by omega))
  obtain ⟨g,hg,hag,hrg⟩ := lowEndpoint_all (b-1) (a/2-1) (by omega) (Or.inr (by omega))
  let F := Math15.Labeling.joinLabel (a/2) (b-1+1) f (fun v => b-1-g v) ∘ concatVertex a (b-1)
  have hbb : b-1+1=b := by omega
  have hc : Complete (a+(b-1)+1) F (pathEnds (a+(b-1)+1)) := by
    apply concat_complete
    apply join_complete hf (complete_reflect hg) haf (by omega) 0 0
    exact Or.inl ⟨by omega,by rw [hrg,hrf]; omega⟩
  have hal : Alpha (a/2+b/2) F (pathEnds (a+(b-1)+1)) := by
    have hh := concat_alpha (join_alpha haf
      (complement_alpha hg.2.1 hag (show (b-1)/2<b-1 by omega))
      (show b-1-(b-1)/2-1≤b-1 by omega) (0 : Fin (a+1)) (0 : Fin (b-1+1))
      (by omega) (by rw [hrg]; omega))
    convert hh using 1 <;> (first | omega | rfl)
  have hr : F ⟨a,by omega⟩=1 := by
    dsimp only [F,Function.comp_apply]
    rw [concat_junction]
    simp [Math15.Labeling.joinLabel,Math15.Labeling.gap,hrf,show 1≤a/2 by omega]
  have hE : a+(b-1)+1=a+b := by omega
  apply pathOne_of_marked hE rfl hc hal
  intro v hv
  have he : v=⟨a,by omega⟩ := Fin.ext hv
  simpa only [he] using hr

/-- Put the marked vertex two positions before the end of a reversed
alternating block. Its label is one, independently of the block length. -/
theorem pathOne_prefix (a b : ℕ) (ha : 3≤a) (hab : a≤b)
    (hsize : (a+2)/2≤(b-3)/2) (hexc : b-3≠4*((a+2)/2)) : PathOne a b := by
  obtain ⟨g,hg,hag,hrg⟩ := lowEndpoint_all (b-3) ((a+2)/2) hsize (Or.inr hexc)
  have hc := prefix_complete (a+2) (b-3) g hg (by omega) hrg
  have hal := prefix_alpha (a+2) (b-3) g hg hag (by omega) hsize hrg
  have hr := prefix_mark_two (a+2) (b-3) g (by omega)
  have hE : a+2+(b-3)+1=a+b := by omega
  have hK : (a+2)/2+(b-3)-(b-3)/2=a/2+b/2 := by omega
  apply pathOne_of_marked hE hK hc hal
  intro v hv
  have he : v=⟨(a+2)-2,by omega⟩ := Fin.ext (by change v.val=a+2-2; omega)
  simpa only [he] using hr

theorem pathOne_ordered (a b : ℕ) (ha : 3≤a) (hab : a≤b) (hex : a≠4 ∨ b≠4) : PathOne a b := by
  by_cases ha4 : a=4
  · subst a
    by_cases hsmall : b≤8
    · have he : b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl
      · simp at hex
      · exact pathOne_4_5
      · exact pathOne_4_6
      · exact pathOne_4_7
      · exact pathOne_4_8
    · by_cases he : b=15
      · subst b; exact pathOne_4_15
      · exact pathOne_prefix 4 b (by omega) hab (by omega) (by omega)
  · by_cases he : b+3=4*(a/2)
    · by_cases hlarge : 8≤a
      · exact pathOne_prefix a b ha hab (by omega) (by omega)
      · have hx : (a=5 ∧ b=5) ∨ (a=6 ∧ b=9) ∨ (a=7 ∧ b=9) := by omega
        rcases hx with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact pathOne_5_5
        · exact pathOne_6_9
        · exact pathOne_7_9
    · exact pathOne_join a b ha hab ha4 he

def reversePathVertex (n : ℕ) (v : Fin (n+1)) : Fin (n+1) := ⟨n-v.val,by omega⟩
def reversePathEdge (n : ℕ) (e : Fin n) : Fin n := ⟨n-1-e.val,by omega⟩

theorem reversePathVertex_bijective (n : ℕ) : Function.Bijective (reversePathVertex n) := by
  apply bijective_of_injective_equal_card
  · intro v w he; apply Fin.ext; have := congrArg Fin.val he; dsimp [reversePathVertex] at this; omega
  · rfl

theorem reversePathEdge_bijective (n : ℕ) : Function.Bijective (reversePathEdge n) := by
  apply bijective_of_injective_equal_card
  · intro v w he; apply Fin.ext; have := congrArg Fin.val he; dsimp [reversePathEdge] at this; omega
  · rfl

theorem reversePath_endpoints (n : ℕ) (e : Fin n) :
    (reversePathVertex n (pathEnds n e).1,reversePathVertex n (pathEnds n e).2)=
      ((pathEnds n (reversePathEdge n e)).2,(pathEnds n (reversePathEdge n e)).1) := by
  simp [reversePathVertex,reversePathEdge,pathEnds,Prod.ext_iff,Fin.ext_iff]; omega

theorem path_reverse_complete {n : ℕ} {f : Fin (n+1) → ℕ}
    (h : Complete n f (pathEnds n)) :
    Complete n (f ∘ reversePathVertex n) (pathEnds n) := by
  apply complete_reindex h _ (reversePathVertex_bijective n) _ (reversePathEdge_bijective n)
  intro e
  have he := reversePath_endpoints n e
  have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
  dsimp only at h1 h2
  rw [h1,h2,Nat.dist_comm]

theorem path_reverse_alpha {n k : ℕ} {f : Fin (n+1) → ℕ}
    (h : Alpha k f (pathEnds n)) : Alpha k (f ∘ reversePathVertex n) (pathEnds n) := by
  intro e
  have hh := h (reversePathEdge n e)
  have he := reversePath_endpoints n e
  have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
  dsimp only at h1 h2
  dsimp only [Function.comp_apply]
  rw [h1,h2]; exact hh.symm

theorem pathOne_swap {a b : ℕ} (h : PathOne a b) : PathOne b a := by
  obtain ⟨f,hf,ha,hr⟩ := h
  apply pathOne_of_marked (Nat.add_comm a b) (by omega) (path_reverse_complete hf) (path_reverse_alpha ha)
  intro v hv
  have he : reversePathVertex (a+b) v=pathJunction a b := by
    apply Fin.ext; simp only [reversePathVertex,pathJunction]; omega
  simpa only [Function.comp_apply,he] using hr

theorem path_interior_one_except44 (a b : ℕ) (ha : 3≤a) (hb : 3≤b)
    (hex : a≠4 ∨ b≠4) : PathOne a b := by
  by_cases hab : a≤b
  · exact pathOne_ordered a b ha hab hex
  · exact pathOne_swap (pathOne_ordered b a hb (by omega) hex.symm)

/-- The endpoint construction and the interior-one path construction give
center one unless the two selected path arms are both four. -/
theorem spider_center_one_except44 (a b c : ℕ) (ha : 3≤a) (hb : a≤b) (hc : b≤c+1)
    (hex : a≠4 ∨ b≠4) :
    ∃ f : Fin (a+b+1) ⊕ Fin (c+1) → ℕ,
      Complete (a+b+c+1) f (spiderEnds a b c) ∧ f (.inl (pathJunction a b))=1 := by
  obtain ⟨f,hf,haf,huf⟩ := path_interior_one_except44 a b ha (by omega) hex
  have hk : 1≤a/2+b/2 := by omega
  have hkn : a/2+b/2≤a+b := by omega
  have hkc : a/2+b/2≤c+1 := by omega
  obtain ⟨g,hg,hvg⟩ := path_endpoint_flexible c (c+1-(a/2+b/2)) (by omega)
  exact attach_at_one hf hg haf hk hkn hkc (pathJunction a b) 0 huf hvg

end Math15Source10
#print axioms Math15Source10.path_interior_one_except44
#print axioms Math15Source10.spider_center_one_except44
