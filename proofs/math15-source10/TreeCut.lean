import TreeChains

namespace Math15Source10
open SimpleGraph

theorem embedding_degree_le {V W : Type*} [Fintype V] [Fintype W]
    {H : SimpleGraph V} {G : SimpleGraph W} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (e : H ↪g G) (x : V) : H.degree x≤G.degree (e x) := by
  simpa only [←SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective (e.mapNeighborSet x) (e.mapNeighborSet x).injective

theorem embedding_degree_lt_missing {V W : Type*} [Fintype V] [Fintype W]
    {H : SimpleGraph V} {G : SimpleGraph W} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (e : H ↪g G) (x : V) (y : W) (hxy : G.Adj (e x) y) (hy : ∀z,e z≠y) :
    H.degree x<G.degree (e x) := by
  have hn : ¬Function.Surjective (e.mapNeighborSet x) := by
    intro hs
    obtain ⟨z,hz⟩ := hs ⟨y,hxy⟩
    exact hy z.val (congrArg Subtype.val hz)
  simpa only [←SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_lt_of_injective_not_surjective (e.mapNeighborSet x) (e.mapNeighborSet x).injective hn

def componentEmbedding {V : Type*} {G : SimpleGraph V} (s : Set V)
    (C : (G.induce s).ConnectedComponent) : C.toSimpleGraph ↪g G :=
  (SimpleGraph.Embedding.induce s).comp (SimpleGraph.Embedding.induce C.supp)

/-- Every component left by deleting a nonempty set has an attachment to
that set. Connectedness supplies the edge; no tree assumption is needed. -/
theorem component_has_boundary {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    (s : Set V) (r : V) (hr : r∉s) (C : (G.induce s).ConnectedComponent) :
    ∃ (x : C) (y : V), y∉s ∧ G.Adj (componentEmbedding s C x) y := by
  classical
  by_contra h
  push_neg at h
  let t : Set V := Set.range (componentEmbedding s C)
  obtain ⟨x,hx⟩ := C.nonempty_supp
  let xC : C := ⟨x,hx⟩
  have hall : ∀y,y∈t := by
    apply connected_closed_all hc t (componentEmbedding s C xC) ⟨xC,rfl⟩
    intro a ha b hab
    obtain ⟨z,rfl⟩ := ha
    have hb : b∈s := by
      by_contra hbs
      exact h z b hbs hab
    have hadj : (G.induce s).Adj z.val ⟨b,hb⟩ := hab
    have hbc : (⟨b,hb⟩ : s)∈C.supp := (C.mem_supp_congr_adj hadj).mp z.property
    exact ⟨⟨⟨b,hb⟩,hbc⟩,rfl⟩
  obtain ⟨z,hz⟩ := hall r
  exact hr (hz ▸ z.val.property)

/-- If all retained vertices have degree at most two, every component
after a nonempty deletion is a path, rooted at an attachment vertex. -/
theorem deleted_components_are_paths {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hc : G.Connected) (s : Set V) (r : V) (hr : r∉s)
    (hd : ∀x∈s,G.degree x≤2) (C : (G.induce s).ConnectedComponent) :
    ∃ (x z : C) (y : V) (p : C.toSimpleGraph.Walk x z),
      y∉s ∧ G.Adj (componentEmbedding s C x) y ∧ p.IsPath ∧ ∀v,v∈p.support := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  obtain ⟨x,y,hy,hxy⟩ := component_has_boundary hc s r hr C
  have hx : C.toSimpleGraph.degree x≤1 := by
    have hh := embedding_degree_lt_missing (componentEmbedding s C) x y hxy
      (fun z hz => hy (hz ▸ z.val.property))
    have hh' := hd x.val.val x.val.property
    change C.toSimpleGraph.degree x<G.degree x.val.val at hh
    omega
  have hdeg (z : C) : C.toSimpleGraph.degree z≤2 :=
    (embedding_degree_le (componentEmbedding s C) z).trans (hd z.val.val z.val.property)
  obtain ⟨z,p,hp,hspan⟩ := degree_two_rooted_spanning_path C.connected_toSimpleGraph x hx hdeg
  exact ⟨x,z,y,p,hy,hxy,hp,hspan⟩

end Math15Source10
#print axioms Math15Source10.deleted_components_are_paths
