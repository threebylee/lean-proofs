import HubStructure

namespace Math15Source10
open SimpleGraph

theorem component_other_boundary_last {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {u v : V} (huv : u≠v)
    (hd : ∀x∈outsideTwo u v,G.degree x≤2)
    (C : (G.induce (outsideTwo u v)).ConnectedComponent)
    {a b z : C} {p : C.toSimpleGraph.Walk a b} (hp : p.IsPath) (hspan : ∀x,x∈p.support)
    (ha : G.Adj u (componentEmbedding (outsideTwo u v) C a))
    (hz : G.Adj v (componentEmbedding (outsideTwo u v) C z)) : z=b := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  rcases component_boundary_at_endpoints (outsideTwo u v) hd C hp hspan
    (by simp [outsideTwo] : v∉outsideTwo u v) hz.symm with hza | hzb
  · subst z
    have hlen : p.length=0 := by
      by_contra hn
      have hadj := p.adj_getVert_succ (show 0<p.length by omega)
      simp only [Walk.getVert_zero,zero_add] at hadj
      have hg : G.Adj (componentEmbedding (outsideTwo u v) C a)
          (componentEmbedding (outsideTwo u v) C (p.getVert 1)) :=
        (componentEmbedding (outsideTwo u v) C).map_adj_iff.mpr hadj
      rcases two_neighbors_exhaust (hd a.val.val a.val.property) huv ha.symm hz.symm hg with he | he
      · exact (p.getVert 1).val.property.1 he
      · exact (p.getVert 1).val.property.2 he
    exact p.eq_of_length_eq_zero hlen
  · exact hzb

/-- An indexed component path with its complete internal and hub adjacency
description. All graph facts follow from the original tree hypotheses. -/
theorem rooted_component_chain {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (ht : G.IsTree) {u v : V} (huv : u≠v)
    (hd : ∀x∈outsideTwo u v,G.degree x≤2)
    (C : (G.induce (outsideTwo u v)).ConnectedComponent) (hC : ComponentAttached C u) :
    ∃ (k : ℕ) (e : Fin (k+1) ≃ C),
      (∀i j,C.toSimpleGraph.Adj (e i) (e j) ↔ i.val+1=j.val ∨ j.val+1=i.val) ∧
      (∀i,G.Adj u (componentEmbedding (outsideTwo u v) C (e i)) ↔ i.val=0) ∧
      (∀i,G.Adj v (componentEmbedding (outsideTwo u v) C (e i)) ↔
        ComponentAttached C v ∧ i.val=k) := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  obtain ⟨a,ha⟩ := hC
  have hda : C.toSimpleGraph.degree a≤1 := by
    have hh := embedding_degree_lt_missing (componentEmbedding (outsideTwo u v) C) a u ha.symm
      (fun z => z.val.property.1)
    have hg := hd a.val.val a.val.property
    change C.toSimpleGraph.degree a<G.degree a.val.val at hh
    omega
  have hdC (z : C) : C.toSimpleGraph.degree z≤2 :=
    (embedding_degree_le (componentEmbedding (outsideTwo u v) C) z).trans (hd z.val.val z.val.property)
  obtain ⟨b,p,hp,hspan⟩ := degree_two_rooted_spanning_path C.connected_toSimpleGraph a hda hdC
  let e := spanningPathEquiv p hp hspan
  have he (i : Fin (p.length+1)) : e i=p.getVert i.val := rfl
  have h0 : e 0=a := by simp [he]
  have hlast : e ⟨p.length,by omega⟩=b := by simp [he]
  refine ⟨p.length,e,?_,?_,?_⟩
  · intro i j
    exact spanning_path_adj_iff ((ht.IsAcyclic.induce (outsideTwo u v)).induce C.supp) hp i j
  · intro i
    constructor
    · intro hi
      have hei : e i=a := component_boundary_unique ht.IsAcyclic (outsideTwo u v) C
        (by simp [outsideTwo] : u∉outsideTwo u v) hi ha
      have hh : i=0 := e.injective (hei.trans h0.symm)
      exact congrArg Fin.val hh
    · intro hi
      have hh : i=0 := Fin.ext hi
      simpa only [hh,h0] using ha
  · intro i
    constructor
    · intro hi
      have hib : e i=b := component_other_boundary_last huv hd C hp hspan ha hi
      have hh : i=⟨p.length,by omega⟩ := e.injective (hib.trans hlast.symm)
      exact ⟨⟨e i,hi⟩,congrArg Fin.val hh⟩
    · rintro ⟨⟨z,hz⟩,hi⟩
      have hzb : z=b := component_other_boundary_last huv hd C hp hspan ha hz
      have hh : i=⟨p.length,by omega⟩ := Fin.ext hi
      simpa only [hh,hlast,hzb] using hz

end Math15Source10
#print axioms Math15Source10.rooted_component_chain
