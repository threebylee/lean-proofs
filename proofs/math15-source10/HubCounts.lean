import HubBoundary

namespace Math15Source10
open SimpleGraph

abbrev HubIncidence {V : Type*} (G : SimpleGraph V) (u v : V) :=
  {x : outsideTwo u v // G.Adj u x.val}

def incidenceComponent {V : Type*} {G : SimpleGraph V} (u v : V) (x : HubIncidence G u v) :
    {C : (G.induce (outsideTwo u v)).ConnectedComponent // ComponentAttached C u} :=
  ⟨_,⟨⟨x.val,rfl⟩,x.property⟩⟩

theorem incidenceComponent_bijective {V : Type*} {G : SimpleGraph V} (ht : G.IsAcyclic)
    (u v : V) : Function.Bijective (incidenceComponent (G:=G) u v) := by
  constructor
  · intro x y he
    have hc := congrArg Subtype.val he
    let C := (G.induce (outsideTwo u v)).connectedComponentMk x.val
    have hy : y.val∈C.supp := hc.symm
    have hh := component_boundary_unique ht (outsideTwo u v) C (r:=u) (by simp [outsideTwo])
      (x:=⟨x.val,rfl⟩) (y:=⟨y.val,hy⟩) x.property y.property
    have hxy : x.val=y.val := congrArg (fun z : C => z.val) hh
    exact Subtype.ext hxy
  · rintro ⟨C,x,hx⟩
    refine ⟨⟨x.val,hx⟩,?_⟩
    apply Subtype.ext
    exact x.property

noncomputable def incidenceComponentEquiv {V : Type*} {G : SimpleGraph V} (ht : G.IsAcyclic)
    (u v : V) : HubIncidence G u v ≃
      {C : (G.induce (outsideTwo u v)).ConnectedComponent // ComponentAttached C u} :=
  Equiv.ofBijective _ (incidenceComponent_bijective ht u v)

def incidenceNeighbor {V : Type*} {G : SimpleGraph V} (u v : V) (x : HubIncidence G u v) :
    G.neighborSet u := ⟨x.val.val,x.property⟩

theorem incidenceNeighbor_injective {V : Type*} {G : SimpleGraph V} (u v : V) :
    Function.Injective (incidenceNeighbor (G:=G) u v) := by
  intro x y he
  have hh : x.val.val=y.val.val := congrArg (fun z : G.neighborSet u => z.val) he
  exact Subtype.ext (Subtype.ext hh)

theorem incidence_card_nonadjacent {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {u v : V} (hnot : ¬G.Adj u v) :
    Nat.card (HubIncidence G u v)=G.degree u := by
  classical
  letI : Fintype (HubIncidence G u v) := Fintype.ofFinite _
  have he : Function.Bijective (incidenceNeighbor (G:=G) u v) := by
    refine ⟨incidenceNeighbor_injective u v,?_⟩
    intro y
    have hy : y.val∈outsideTwo u v := ⟨y.property.ne',by intro hv; exact hnot (hv ▸ y.property)⟩
    exact ⟨⟨⟨y.val,hy⟩,y.property⟩,rfl⟩
  rw [Nat.card_eq_fintype_card,←SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (Equiv.ofBijective _ he)

def incidenceOptionNeighbor {V : Type*} {G : SimpleGraph V} {u v : V} (ha : G.Adj u v) :
    Option (HubIncidence G u v) → G.neighborSet u
  | none => ⟨v,ha⟩
  | some x => incidenceNeighbor u v x

theorem incidence_card_adjacent {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {u v : V} (ha : G.Adj u v) :
    Nat.card (HubIncidence G u v)+1=G.degree u := by
  classical
  letI : Fintype (HubIncidence G u v) := Fintype.ofFinite _
  have he : Function.Bijective (incidenceOptionNeighbor ha) := by
    constructor
    · intro x y hxy
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some y => exact (y.val.property.2 (congrArg Subtype.val hxy).symm).elim
      | some x =>
        cases y with
        | none => exact (x.val.property.2 (congrArg Subtype.val hxy)).elim
        | some y => exact congrArg some (incidenceNeighbor_injective u v hxy)
    · intro y
      by_cases hy : y.val=v
      · exact ⟨none,Subtype.ext hy.symm⟩
      · exact ⟨some ⟨⟨y.val,⟨y.property.ne',hy⟩⟩,y.property⟩,rfl⟩
  have hh := Fintype.card_congr (Equiv.ofBijective _ he)
  simpa only [Fintype.card_option,←SimpleGraph.card_neighborSet_eq_degree,Nat.card_eq_fintype_card] using hh

theorem attached_components_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (ht : G.IsAcyclic) (u v : V) :
    Nat.card {C : (G.induce (outsideTwo u v)).ConnectedComponent // ComponentAttached C u}+
      (if G.Adj u v then 1 else 0)=G.degree u := by
  classical
  rw [←Nat.card_congr (incidenceComponentEquiv ht u v)]
  by_cases ha : G.Adj u v
  · simpa [ha] using incidence_card_adjacent ha
  · simpa [ha] using incidence_card_nonadjacent ha

end Math15Source10
#print axioms Math15Source10.attached_components_card
