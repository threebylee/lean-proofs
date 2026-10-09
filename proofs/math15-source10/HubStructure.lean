import HubCounts

namespace Math15Source10
open SimpleGraph

theorem bridge_components_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (ht : G.IsTree) {u v : V} (huv : u≠v) :
    Nat.card {C : (G.induce (outsideTwo u v)).ConnectedComponent //
      ComponentAttached C u ∧ ComponentAttached C v} = if G.Adj u v then 0 else 1 := by
  classical
  letI : Fintype (G.induce (outsideTwo u v)).ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  by_cases ha : G.Adj u v
  · rw [if_pos ha]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro C hC
    have hh := (Finset.mem_filter.mp hC).2
    exact adjacent_hubs_no_bridge_component ht.IsAcyclic huv ha C hh.1 hh.2
  · rw [if_neg ha]
    obtain ⟨C,hu,hv⟩ := nonadjacent_hubs_bridge_exists ht.isConnected huv ha
    apply Finset.card_eq_one.mpr
    refine ⟨C,?_⟩
    ext D
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro hD; exact bridge_component_unique ht.IsAcyclic huv D C hD.1 hD.2 hu hv
    · rintro rfl; exact ⟨hu,hv⟩

theorem terminal_components_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (ht : G.IsTree) {u v : V} (huv : u≠v) :
    Nat.card {C : (G.induce (outsideTwo u v)).ConnectedComponent //
      ComponentAttached C u ∧ ¬ComponentAttached C v}+1=G.degree u := by
  classical
  letI : Fintype (G.induce (outsideTwo u v)).ConnectedComponent := Fintype.ofFinite _
  have hb := bridge_components_card ht huv
  have ha := attached_components_card ht.IsAcyclic u v
  have hp := Finset.card_filter_add_card_filter_not
    (s:=Finset.univ.filter (fun C : (G.induce (outsideTwo u v)).ConnectedComponent => ComponentAttached C u))
    (fun C => ComponentAttached C v)
  simp only [Finset.filter_filter] at hp
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype] at hb ha ⊢
  by_cases hadj : G.Adj u v <;> simp only [hadj,↓reduceIte] at hb ha <;> omega

theorem validator_degree_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n) :
    Math15.Graceful.degree G x=G.degree x := by
  classical
  unfold Math15.Graceful.degree
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp

/-- Three terminal chain components at the degree-four hub, two at the
degree-three hub, and either a direct bridge or one bridge component. -/
theorem branch43_component_counts {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (ht : G.IsTree)
    {u v : Fin n} (hb : Math15.Graceful.Branch43 G u v) :
    Nat.card {C : (G.induce (outsideTwo u v)).ConnectedComponent //
      ComponentAttached C u ∧ ¬ComponentAttached C v}=3 ∧
    Nat.card {C : (G.induce (outsideTwo u v)).ConnectedComponent //
      ComponentAttached C v ∧ ¬ComponentAttached C u}=2 ∧
    Nat.card {C : (G.induce (outsideTwo u v)).ConnectedComponent //
      ComponentAttached C u ∧ ComponentAttached C v}=(if G.Adj u v then 0 else 1) := by
  classical
  have h1 := terminal_components_card ht hb.1
  have h2 := terminal_components_card ht hb.1.symm
  have hs : outsideTwo v u=outsideTwo u v := by ext x; exact and_comm
  rw [hs] at h2
  have hu := hb.2.1
  have hv := hb.2.2.1
  rw [validator_degree_eq] at hu hv
  exact ⟨by omega,by omega,bridge_components_card ht hb.1⟩

/-- The component paths and attachment endpoints are consequences of the
canonical Branch43 hypotheses, with no graph-shape assumption. -/
theorem branch43_component_paths {n : ℕ} {G : SimpleGraph (Fin n)} (ht : G.IsTree)
    {u v : Fin n} (hb : Math15.Graceful.Branch43 G u v)
    (C : (G.induce (outsideTwo u v)).ConnectedComponent) :
    ∃ (a b : C) (p : C.toSimpleGraph.Walk a b),p.IsPath ∧ (∀x,x∈p.support) ∧
      ∀ (x : C) (y : Fin n), (y=u ∨ y=v) →
        G.Adj (componentEmbedding (outsideTwo u v) C x) y → x=a ∨ x=b := by
  classical
  have hd : ∀x∈outsideTwo u v,G.degree x≤2 := by
    intro x hx
    rw [←validator_degree_eq]
    exact hb.2.2.2 x hx.1 hx.2
  obtain ⟨a,b,y,p,hy,hxy,hp,hspan⟩ := deleted_components_are_paths ht.isConnected (outsideTwo u v)
    u (by simp [outsideTwo]) hd C
  refine ⟨a,b,p,hp,hspan,?_⟩
  intro x y hy hxy
  apply component_boundary_at_endpoints (outsideTwo u v) hd C hp hspan (y:=y) _ hxy
  rcases hy with rfl | rfl <;> simp [outsideTwo]

end Math15Source10
#print axioms Math15Source10.branch43_component_counts
#print axioms Math15Source10.branch43_component_paths
