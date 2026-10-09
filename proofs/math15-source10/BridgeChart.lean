import HubOrientation

set_option linter.unusedSimpArgs false
namespace Math15Source10
open SimpleGraph

structure BridgeChart {V : Type*} {G : SimpleGraph V} {u v : V} (H : HubCoordinates G u v) where
  length : ℕ
  positive : 1≤length
  vertex : Fin (length+1) → HubChartV H
  injective : Function.Injective vertex
  first : vertex 0=.inl 0
  last : vertex ⟨length,by omega⟩=.inl 1
  edges : ∀i : Fin length,hubChartAdj H (vertex ⟨i.val,by omega⟩) (vertex ⟨i.val+1,by omega⟩)
  disjoint : ∀ (C : HubC G u v),
    ((ComponentAttached C u ∧ ¬ComponentAttached C v) ∨
     (ComponentAttached C v ∧ ¬ComponentAttached C u)) →
    ∀ i j,vertex i≠.inr ⟨C,j⟩
  cover : ∀ (C : HubC G u v),ComponentAttached C u → ComponentAttached C v →
    ∀j,∃i,vertex i=.inr ⟨C,j⟩

def chainBridgeVertex {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v) (i : Fin (H.length C+3)) : HubChartV H :=
  if h : i.val=0 then .inl 0 else if hl : i.val=H.length C+2 then .inl 1
  else .inr ⟨C,orientedBridgeIndex H C ⟨i.val-1,by omega⟩⟩

theorem chainBridgeVertex_injective {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v) : Function.Injective (chainBridgeVertex H C) := by
  intro i j he
  apply Fin.ext
  simp only [chainBridgeVertex] at he
  split_ifs at he <;>
    simp only [Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
      Sigma.mk.inj_iff,heq_eq_eq,true_and] at he
  all_goals try omega
  all_goals try contradiction
  all_goals try norm_num at he
  have hv := congrArg Fin.val ((orientedBridgeIndex_involutive H C).injective he)
  dsimp only at hv
  omega

theorem chainBridgeVertex_edges {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v)
    (hu : ComponentAttached C u) (hv : ComponentAttached C v) (i : Fin (H.length C+2)) :
    hubChartAdj H (chainBridgeVertex H C ⟨i.val,by omega⟩)
      (chainBridgeVertex H C ⟨i.val+1,by omega⟩) := by
  by_cases hi : i.val=0
  · cases hb : H.atU C <;>
      simp [chainBridgeVertex,hi,hubChartAdj,orientedBridgeIndex,hb,hu,hv,Fin.val_rev]
  · by_cases hl : i.val+1=H.length C+2
    · cases hb : H.atU C <;>
        simp [chainBridgeVertex,hi,hl,show i.val≠H.length C+2 by omega,
          show i.val+1≠0 by omega,hubChartAdj,orientedBridgeIndex,hb,hu,hv,Fin.val_rev] <;> omega
    · cases hb : H.atU C <;>
        simp [chainBridgeVertex,hi,hl,show i.val≠H.length C+2 by omega,
          show i.val+1≠0 by omega,show i.val≠H.length C+1 by omega,
          hubChartAdj,orientedBridgeIndex,hb,Fin.val_rev] <;> omega

theorem bridgeChart_exists {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (ht : G.IsTree) {u v : V} (huv : u≠v)
    (H : HubCoordinates G u v) : Nonempty (BridgeChart H) := by
  classical
  by_cases hadj : G.Adj u v
  · refine ⟨⟨1,by omega,Sum.inl,Sum.inl_injective, rfl,rfl,?_,?_,?_⟩⟩
    · intro i; fin_cases i; simp [hubChartAdj,hadj]
    · intro C hC i j; simp
    · intro C hu hv j
      exact (adjacent_hubs_no_bridge_component ht.IsAcyclic huv hadj C hu hv).elim
  · obtain ⟨C,hu,hv⟩ := nonadjacent_hubs_bridge_exists ht.isConnected huv hadj
    refine ⟨⟨H.length C+2,by omega,chainBridgeVertex H C,
      chainBridgeVertex_injective H C,?_,?_,chainBridgeVertex_edges H C hu hv,?_,?_⟩⟩
    · simp [chainBridgeVertex]
    · simp [chainBridgeVertex]
    · intro D hD i j he
      have hCD : C≠D := by
        rintro rfl
        rcases hD with hD | hD
        · exact hD.2 hv
        · exact hD.2 hu
      simp only [chainBridgeVertex] at he
      split_ifs at he <;> try contradiction
      have hh := congrArg (fun x : HubChartV H => match x with | .inl _ => none | .inr z => some z.1) he
      exact hCD (Option.some.inj hh)
    · intro D hDu hDv j
      have hDC := bridge_component_unique ht.IsAcyclic huv D C hDu hDv hu hv
      subst D
      let k := orientedBridgeIndex H C j
      refine ⟨⟨k.val+1,by have := k.isLt; omega⟩,?_⟩
      have hk : k.val+1≠H.length C+2 := by have := k.isLt; omega
      simp only [chainBridgeVertex,show k.val+1≠0 by omega,↓reduceDIte,hk]
      have he : (⟨k.val+1-1,by have := k.isLt; omega⟩ : Fin (H.length C+1))=k := by
        apply Fin.ext
        simp
      rw [he]
      exact congrArg Sum.inr (congrArg (Sigma.mk C) (orientedBridgeIndex_involutive H C j))

end Math15Source10
#print axioms Math15Source10.bridgeChart_exists
