import TreeCut

namespace Math15Source10
open SimpleGraph

/-- A connected subgraph of a tree cannot meet the same outside vertex in
two distinct edges. Otherwise those edges and its path form a cycle. -/
theorem tree_outside_neighbor_unique {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}
    (ht : G.IsAcyclic) (hc : H.Connected) (e : H ↪g G) (r : W)
    (hr : ∀x,e x≠r) {x y : V} (hx : G.Adj r (e x)) (hy : G.Adj r (e y)) : x=y := by
  classical
  obtain ⟨p,hp⟩ := hc.exists_isPath x y
  have hpm : (p.map e.toHom).IsPath := Walk.map_isPath_of_injective e.injective hp
  have hnot : r∉(p.map e.toHom).support := by
    simp only [Walk.support_map,List.mem_map]
    rintro ⟨z,hz,he⟩
    exact hr z he
  have hcons := hpm.cons hnot (h:=hx)
  have heq := ht.path_unique (⟨(p.map e.toHom).cons hx,hcons⟩ : G.Path r (e y))
    ⟨hy.toWalk,Walk.IsPath.of_adj hy⟩
  have hw := congrArg Subtype.val heq
  have hs := congrArg Walk.snd hw
  apply e.injective
  simpa [SimpleGraph.Adj.toWalk,Walk.snd_cons] using hs

theorem path_endpoint_of_degree_le_one {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {a b x : V} {p : G.Walk a b} (hp : p.IsPath)
    (hx : x∈p.support) (hd : G.degree x≤1) : x=a ∨ x=b := by
  classical
  obtain ⟨i,hix,hi⟩ := p.mem_support_iff_exists_getVert.mp hx
  subst x
  by_cases hi0 : i=0
  · subst i; exact Or.inl p.getVert_zero
  · by_cases hil : i=p.length
    · subst i; exact Or.inr p.getVert_length
    · have ha := (p.adj_getVert_succ (show i-1<p.length by omega)).symm
      rw [show i-1+1=i by omega] at ha
      have hb := p.adj_getVert_succ (show i<p.length by omega)
      have he : p.getVert (i-1)=p.getVert (i+1) :=
        Finset.card_le_one.mp hd _ (by simpa using ha) _ (by simpa using hb)
      have hh := hp.getVert_injOn (show i-1≤p.length by omega) (show i+1≤p.length by omega) he
      omega

theorem component_boundary_at_endpoints {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (s : Set V) (hd : ∀x∈s,G.degree x≤2)
    (C : (G.induce s).ConnectedComponent) {a b x : C} {p : C.toSimpleGraph.Walk a b}
    (hp : p.IsPath) (hspan : ∀v,v∈p.support) {y : V} (hy : y∉s)
    (hxy : G.Adj (componentEmbedding s C x) y) : x=a ∨ x=b := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  have hh := embedding_degree_lt_missing (componentEmbedding s C) x y hxy
    (fun z hz => hy (hz ▸ z.val.property))
  have hh' := hd x.val.val x.val.property
  change C.toSimpleGraph.degree x<G.degree x.val.val at hh
  exact path_endpoint_of_degree_le_one hp (hspan x) (by omega)

theorem component_boundary_unique {V : Type*} {G : SimpleGraph V} (ht : G.IsAcyclic)
    (s : Set V) (C : (G.induce s).ConnectedComponent) {r : V} (hr : r∉s)
    {x y : C} (hx : G.Adj r (componentEmbedding s C x))
    (hy : G.Adj r (componentEmbedding s C y)) : x=y :=
  tree_outside_neighbor_unique ht C.connected_toSimpleGraph (componentEmbedding s C) r
    (fun z hz => hr (hz ▸ z.val.property)) hx hy

/-- An exact adjacency description for a spanning path in an acyclic graph. -/
theorem spanning_path_adj_iff {V : Type*} {G : SimpleGraph V} (ht : G.IsAcyclic)
    {a b : V} {p : G.Walk a b} (hp : p.IsPath) (i j : Fin (p.length+1)) :
    G.Adj (p.getVert i.val) (p.getVert j.val) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  constructor
  · exact tree_path_adj_indices ht hp (by omega) (by omega)
  · rintro (h | h)
    · rw [←h]; exact p.adj_getVert_succ (by omega)
    · rw [←h]; exact (p.adj_getVert_succ (by omega)).symm

noncomputable def spanningPathEquiv {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (hs : ∀x,x∈p.support) : Fin (p.length+1) ≃ V :=
  Equiv.ofBijective (fun i : Fin (p.length+1) => p.getVert i.val) (by
    constructor
    · intro i j he; apply Fin.ext
      exact hp.getVert_injOn (show i.val≤p.length by omega) (show j.val≤p.length by omega) he
    · intro x
      obtain ⟨i,hi,hb⟩ := p.mem_support_iff_exists_getVert.mp (hs x)
      exact ⟨⟨i,by omega⟩,hi⟩)

end Math15Source10
#print axioms Math15Source10.tree_outside_neighbor_unique
#print axioms Math15Source10.component_boundary_at_endpoints
#print axioms Math15Source10.spanning_path_adj_iff
