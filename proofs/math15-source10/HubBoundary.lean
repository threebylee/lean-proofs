import TreeBoundary

namespace Math15Source10
open SimpleGraph

def outsideTwo {V : Type*} (u v : V) : Set V := {x | x≠u ∧ x≠v}
def ComponentAttached {V : Type*} {G : SimpleGraph V} {s : Set V}
    (C : (G.induce s).ConnectedComponent) (r : V) : Prop :=
  ∃x : C,G.Adj r (componentEmbedding s C x)

theorem path_through_component {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}
    (hc : H.Connected) (e : H ↪g G) {u v : W} (huv : u≠v)
    (hu : ∀x,e x≠u) (hv : ∀x,e x≠v) {x y : V}
    (hx : G.Adj u (e x)) (hy : G.Adj v (e y)) :
    ∃p : G.Walk u v,p.IsPath ∧ p.snd=e x ∧ 2≤p.length := by
  classical
  obtain ⟨q,hq⟩ := hc.exists_isPath x y
  have hm : (q.map e.toHom).IsPath := Walk.map_isPath_of_injective e.injective hq
  have hnu : u∉(q.map e.toHom).support := by
    simp only [Walk.support_map,List.mem_map]
    rintro ⟨z,hz,he⟩; exact hu z he
  have hp := hm.cons hnu (h:=hx)
  have hnv : v∉((q.map e.toHom).cons hx).support := by
    simp only [Walk.support_cons,List.mem_cons,Walk.support_map,List.mem_map]
    rintro (he | ⟨z,hz,he⟩)
    · exact huv he.symm
    · exact hv z he
  refine ⟨((q.map e.toHom).cons hx).concat hy.symm,hp.concat hnv hy.symm,?_,?_⟩
  · simp [Walk.concat_eq_append,Walk.snd,Walk.getVert_cons]
  · simp [Walk.length_concat]

theorem component_attached_either {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    (u v : V) (C : (G.induce (outsideTwo u v)).ConnectedComponent) :
    ComponentAttached C u ∨ ComponentAttached C v := by
  obtain ⟨x,y,hy,hxy⟩ := component_has_boundary hc (outsideTwo u v) u (by simp [outsideTwo]) C
  have he : y=u ∨ y=v := by
    by_cases hu : y=u
    · exact Or.inl hu
    · exact Or.inr (by by_contra hv; exact hy ⟨hu,hv⟩)
  rcases he with rfl | rfl
  · exact Or.inl ⟨x,hxy.symm⟩
  · exact Or.inr ⟨x,hxy.symm⟩

theorem component_bridge_path {V : Type*} {G : SimpleGraph V} {u v : V} (huv : u≠v)
    (C : (G.induce (outsideTwo u v)).ConnectedComponent)
    (hu : ComponentAttached C u) (hv : ComponentAttached C v) :
    ∃ (x : C) (p : G.Walk u v),p.IsPath ∧ p.snd=componentEmbedding (outsideTwo u v) C x ∧ 2≤p.length := by
  obtain ⟨x,hx⟩ := hu; obtain ⟨y,hy⟩ := hv
  obtain ⟨p,hp,hs,hl⟩ := path_through_component C.connected_toSimpleGraph
    (componentEmbedding (outsideTwo u v) C) huv (fun z => z.val.property.1) (fun z => z.val.property.2) hx hy
  exact ⟨x,p,hp,hs,hl⟩

theorem bridge_component_unique {V : Type*} {G : SimpleGraph V} (ht : G.IsAcyclic)
    {u v : V} (huv : u≠v) (C D : (G.induce (outsideTwo u v)).ConnectedComponent)
    (hCu : ComponentAttached C u) (hCv : ComponentAttached C v)
    (hDu : ComponentAttached D u) (hDv : ComponentAttached D v) : C=D := by
  obtain ⟨x,p,hp,hs,_⟩ := component_bridge_path huv C hCu hCv
  obtain ⟨y,q,hq,htail,_⟩ := component_bridge_path huv D hDu hDv
  have he : p=q := congrArg Subtype.val (ht.path_unique (⟨p,hp⟩ : G.Path u v) ⟨q,hq⟩)
  have hxy : x.val=y.val := by
    apply Subtype.ext
    simpa only [hs,htail] using congrArg Walk.snd he
  have hC : (G.induce (outsideTwo u v)).connectedComponentMk x.val=C := x.property
  have hD : (G.induce (outsideTwo u v)).connectedComponentMk y.val=D := y.property
  rw [←hC,←hD,hxy]

theorem adjacent_hubs_no_bridge_component {V : Type*} {G : SimpleGraph V} (ht : G.IsAcyclic)
    {u v : V} (huv : u≠v) (hadj : G.Adj u v)
    (C : (G.induce (outsideTwo u v)).ConnectedComponent)
    (hu : ComponentAttached C u) : ¬ComponentAttached C v := by
  intro hv
  obtain ⟨x,p,hp,hs,hl⟩ := component_bridge_path huv C hu hv
  have he : p=hadj.toWalk := congrArg Subtype.val
    (ht.path_unique (⟨p,hp⟩ : G.Path u v) ⟨hadj.toWalk,Walk.IsPath.of_adj hadj⟩)
  rw [he] at hl
  simp [SimpleGraph.Adj.toWalk] at hl

theorem nonadjacent_hubs_bridge_exists {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    {u v : V} (huv : u≠v) (hnot : ¬G.Adj u v) :
    ∃ C : (G.induce (outsideTwo u v)).ConnectedComponent,
      ComponentAttached C u ∧ ComponentAttached C v := by
  classical
  by_contra h
  push_neg at h
  let s : Set V := {x | x=u ∨ ∃ hx : x∈outsideTwo u v,
    ComponentAttached ((G.induce (outsideTwo u v)).connectedComponentMk ⟨x,hx⟩) u}
  have hall : ∀x,x∈s := by
    apply connected_closed_all hc s u (Or.inl rfl)
    intro a ha b hab
    rcases ha with ha | ⟨ha,hau⟩
    · subst a
      by_cases hbu : b=u
      · exact Or.inl hbu
      · have hb : b∈outsideTwo u v := ⟨hbu,by intro he; subst b; exact hnot hab⟩
        exact Or.inr ⟨hb,⟨⟨⟨b,hb⟩,rfl⟩,hab⟩⟩
    · by_cases hbu : b=u
      · exact Or.inl hbu
      · have hb : b∈outsideTwo u v := ⟨hbu,by
          intro he; subst b
          exact h _ hau ⟨⟨⟨a,ha⟩,rfl⟩,hab.symm⟩⟩
        have hh : (G.induce (outsideTwo u v)).connectedComponentMk ⟨a,ha⟩=
            (G.induce (outsideTwo u v)).connectedComponentMk ⟨b,hb⟩ :=
          ConnectedComponent.sound (show (G.induce (outsideTwo u v)).Adj ⟨a,ha⟩ ⟨b,hb⟩ from hab).reachable
        exact Or.inr ⟨hb,hh ▸ hau⟩
  rcases hall v with hv | ⟨hv,_⟩
  · exact huv hv.symm
  · exact hv.2 rfl

end Math15Source10
#print axioms Math15Source10.bridge_component_unique
#print axioms Math15Source10.adjacent_hubs_no_bridge_component
#print axioms Math15Source10.nonadjacent_hubs_bridge_exists
