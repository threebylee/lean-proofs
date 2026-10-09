import GraphPresentation

namespace Math15Source10
open Finset SimpleGraph

theorem validator_edgeCount_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Math15.Graceful.edgeCount G = G.edgeFinset.card := by
  classical
  let S := (univ : Finset (Fin n × Fin n)).filter (fun p => p.1<p.2 ∧ G.Adj p.1 p.2)
  have him : S.image Sym2.mk=G.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [mem_image,mem_edgeFinset,mem_edgeSet]
      constructor
      · rintro ⟨⟨a,b⟩,hp,he⟩
        have hab := (mem_filter.mp hp).2
        rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hab.2
        · exact hab.2.symm
      · intro hxy
        by_cases h : x<y
        · exact ⟨(x,y),by simp [S,h,hxy],rfl⟩
        · exact ⟨(y,x),by simp [S,lt_of_le_of_ne (le_of_not_gt h) hxy.ne.symm,hxy.symm],Sym2.eq_swap⟩
  have hin : Set.InjOn Sym2.mk (S : Set (Fin n × Fin n)) := by
    rintro ⟨a,b⟩ hp ⟨c,d⟩ hq he
    have hp' := (mem_filter.mp hp).2.1
    have hq' := (mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · exact (lt_asymm hp' hq').elim
  rw [←him,card_image_of_injOn hin]
  unfold Math15.Graceful.edgeCount S
  congr 1
  ext p
  simp

/-- A spanning bijection that carries every certificate edge into a tree
already carries all its edges: both edge sets have one fewer element than
the common vertex set. This removes the reverse adjacency proof obligation. -/
theorem graceful_of_tree_embedding {V E : Type*} [Fintype V] [Fintype E]
    {n m : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (G : SimpleGraph (Fin n)) (ht : G.IsTree)
    (e : V ≃ Fin n) (hAdj : ∀i,G.Adj (e (ends i).1) (e (ends i).2)) :
    Math15.Graceful.IsGraceful G := by
  classical
  have hg := Math15.Labeling.good_reindex_vertices h.good e
  let F := Math15.Labeling.graphOfGood hg
  have hle : F≤G := by
    intro x y hxy
    obtain ⟨i,hi | hi⟩ := (graphOfGood_adj_iff hg x y).mp hxy
    · have hh := hAdj i
      have h1 := congrArg Prod.fst hi; have h2 := congrArg Prod.snd hi
      dsimp only at h1 h2
      rw [h1,h2]
      exact hh
    · have hh := (hAdj i).symm
      have h1 := congrArg Prod.fst hi; have h2 := congrArg Prod.snd hi
      dsimp only at h1 h2
      rw [h1,h2]
      exact hh
  have hcardV : Fintype.card V=m+1 := by
    let f' : V → Fin (m+1) := fun v => ⟨f v,by have := h.2.1 v; omega⟩
    have hb : Function.Bijective f' := by
      constructor
      · intro x y he; exact h.1 (congrArg Fin.val he)
      · intro k; obtain ⟨v,hv⟩ := h.2.2.1 k.val (by omega)
        exact ⟨v,Fin.ext hv⟩
    simpa using Fintype.card_congr (Equiv.ofBijective f' hb)
  have hmn : n=m+1 := by
    have hh := Fintype.card_congr e
    simpa [hcardV] using hh.symm
  have hF : F.edgeFinset.card=m := by
    rw [←validator_edgeCount_eq]
    exact (Math15.Labeling.graphOfGood_count hg).trans (complete_edge_card h)
  have hG : G.edgeFinset.card=m := by
    have hh := ht.card_edgeFinset
    simp only [Fintype.card_fin] at hh
    omega
  have heq : F=G := edgeFinset_inj.mp
    (eq_of_subset_of_card_le (edgeFinset_mono hle) (by omega))
  rw [←heq]
  exact Math15.Labeling.graphOfGood_isGraceful hg (complete_edge_card h)

end Math15Source10
#print axioms Math15Source10.graceful_of_tree_embedding
