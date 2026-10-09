import ComponentChains

namespace Math15Source10
open SimpleGraph

abbrev HubC {V : Type*} (G : SimpleGraph V) (u v : V) :=
  (G.induce (outsideTwo u v)).ConnectedComponent

/-- Coordinates for every retained path component. `atU` says which hub
is adjacent to coordinate zero. The complete attachment relations are stored. -/
structure HubCoordinates {V : Type*} (G : SimpleGraph V) (u v : V) where
  length : HubC G u v → ℕ
  coord : ∀ C : HubC G u v, Fin (length C+1) ≃ C
  atU : HubC G u v → Bool
  internal : ∀ (C : HubC G u v) (i j : Fin (length C+1)),C.toSimpleGraph.Adj (coord C i) (coord C j) ↔
    i.val+1=j.val ∨ j.val+1=i.val
  at_left : ∀ (C : HubC G u v) (i : Fin (length C+1)),G.Adj u (componentEmbedding (outsideTwo u v) C (coord C i)) ↔
    if atU C then i.val=0 else ComponentAttached C u ∧ i.val=length C
  at_right : ∀ (C : HubC G u v) (i : Fin (length C+1)),G.Adj v (componentEmbedding (outsideTwo u v) C (coord C i)) ↔
    if atU C then ComponentAttached C v ∧ i.val=length C else i.val=0

theorem hub_coordinates_exist {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (ht : G.IsTree) {u v : V} (huv : u≠v)
    (hd : ∀x∈outsideTwo u v,G.degree x≤2) : Nonempty (HubCoordinates G u v) := by
  classical
  have each (C : HubC G u v) : ∃ (k : ℕ) (e : Fin (k+1) ≃ C) (b : Bool),
      (∀i j,C.toSimpleGraph.Adj (e i) (e j) ↔ i.val+1=j.val ∨ j.val+1=i.val) ∧
      (∀i,G.Adj u (componentEmbedding (outsideTwo u v) C (e i)) ↔
        if b then i.val=0 else ComponentAttached C u ∧ i.val=k) ∧
      (∀i,G.Adj v (componentEmbedding (outsideTwo u v) C (e i)) ↔
        if b then ComponentAttached C v ∧ i.val=k else i.val=0) := by
    by_cases hu : ComponentAttached C u
    · obtain ⟨k,e,hi,h0,hl⟩ := rooted_component_chain ht huv hd C hu
      exact ⟨k,e,true,hi,by simpa using h0,by simpa using hl⟩
    · have hv : ComponentAttached C v := (component_attached_either ht.isConnected u v C).resolve_left hu
      have hs : outsideTwo v u=outsideTwo u v := by ext x; exact and_comm
      have hd' : ∀x∈outsideTwo v u,G.degree x≤2 := by simpa only [hs] using hd
      have hh := rooted_component_chain ht huv.symm hd'
      rw [hs] at hh
      obtain ⟨k,e,hi,h0,hl⟩ := hh C hv
      exact ⟨k,e,false,hi,by simpa using hl,by simpa using h0⟩
  choose k e b hi h0 hl using each
  exact ⟨⟨k,e,b,hi,h0,hl⟩⟩

def hubSumMap {V : Type*} (u v : V) : Fin 2 ⊕ outsideTwo u v → V
  | .inl i => if i.val=0 then u else v
  | .inr x => x.val

theorem hubSumMap_bijective {V : Type*} {u v : V} (huv : u≠v) :
    Function.Bijective (hubSumMap u v) := by
  constructor
  · intro x y he
    rcases x with x | x <;> rcases y with y | y
    · fin_cases x <;> fin_cases y <;> simp_all [hubSumMap]
    · fin_cases x <;> simp [hubSumMap] at he
      · exact (y.property.1 he.symm).elim
      · exact (y.property.2 he.symm).elim
    · fin_cases y <;> simp [hubSumMap] at he
      · exact (x.property.1 he).elim
      · exact (x.property.2 he).elim
    · exact congrArg Sum.inr (Subtype.ext he)
  · intro x
    by_cases hu : x=u
    · exact ⟨.inl 0,by simp [hubSumMap,hu]⟩
    · by_cases hv : x=v
      · exact ⟨.inl 1,by simp [hubSumMap,hv]⟩
      · exact ⟨.inr ⟨x,hu,hv⟩,rfl⟩

noncomputable def hubSumEquiv {V : Type*} {u v : V} (huv : u≠v) :
    (Fin 2 ⊕ outsideTwo u v) ≃ V := Equiv.ofBijective _ (hubSumMap_bijective huv)

noncomputable def componentCoordinateEquiv {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) : (Σ C : HubC G u v, Fin (H.length C+1)) ≃ outsideTwo u v :=
  (Equiv.sigmaCongrRight H.coord).trans (Equiv.sigmaFiberEquiv (G.induce (outsideTwo u v)).connectedComponentMk)

noncomputable def hubCoordinateEquiv {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (huv : u≠v) :
    (Fin 2 ⊕ (Σ C : HubC G u v,Fin (H.length C+1))) ≃ V :=
  (Equiv.sumCongr (Equiv.refl _) (componentCoordinateEquiv H)).trans (hubSumEquiv huv)

theorem hubCoordinateEquiv_component {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (huv : u≠v) (C : HubC G u v) (i : Fin (H.length C+1)) :
    hubCoordinateEquiv H huv (.inr ⟨C,i⟩)=componentEmbedding (outsideTwo u v) C (H.coord C i) := rfl

theorem different_components_not_adj {V : Type*} {G : SimpleGraph V} {s : Set V}
    {C D : (G.induce s).ConnectedComponent} (hCD : C≠D) (x : C) (y : D) :
    ¬G.Adj (componentEmbedding s C x) (componentEmbedding s D y) := by
  intro h
  have hh := ConnectedComponent.sound (show (G.induce s).Adj x.val y.val from h).reachable
  have hx : (G.induce s).connectedComponentMk x.val=C := x.property
  have hy : (G.induce s).connectedComponentMk y.val=D := y.property
  exact hCD (hx.symm.trans (hh.trans hy))

theorem branch43_has_coordinates {n : ℕ} {G : SimpleGraph (Fin n)} (ht : G.IsTree)
    {u v : Fin n} (hb : Math15.Graceful.Branch43 G u v) : Nonempty (HubCoordinates G u v) := by
  classical
  apply hub_coordinates_exist ht hb.1
  intro x hx
  rw [←validator_degree_eq]
  exact hb.2.2.2 x hx.1 hx.2

end Math15Source10
#print axioms Math15Source10.hub_coordinates_exist
#print axioms Math15Source10.branch43_has_coordinates
#print axioms Math15Source10.different_components_not_adj
