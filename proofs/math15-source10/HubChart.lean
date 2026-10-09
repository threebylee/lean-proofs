import HubNormalForm

namespace Math15Source10
open SimpleGraph

abbrev HubChartV {V : Type*} {G : SimpleGraph V} {u v : V} (H : HubCoordinates G u v) :=
  Fin 2 ⊕ (Σ C : HubC G u v,Fin (H.length C+1))

def hubChartAdj {V : Type*} {G : SimpleGraph V} {u v : V} (H : HubCoordinates G u v) :
    HubChartV H → HubChartV H → Prop
  | .inl i,.inl j => i≠j ∧ G.Adj u v
  | .inl i,.inr ⟨C,j⟩ =>
      if i.val=0 then (if H.atU C then j.val=0 else ComponentAttached C u ∧ j.val=H.length C)
      else (if H.atU C then ComponentAttached C v ∧ j.val=H.length C else j.val=0)
  | .inr ⟨C,j⟩,.inl i =>
      if i.val=0 then (if H.atU C then j.val=0 else ComponentAttached C u ∧ j.val=H.length C)
      else (if H.atU C then ComponentAttached C v ∧ j.val=H.length C else j.val=0)
  | .inr ⟨C,i⟩,.inr ⟨D,j⟩ => C=D ∧ (i.val+1=j.val ∨ j.val+1=i.val)

/-- Exact adjacency in the universal chain coordinates: there are no hidden
edges or omitted vertices. The coordinate equivalence is a genuine bijection. -/
theorem hub_chart_adj_iff {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (huv : u≠v) (x y : HubChartV H) :
    G.Adj (hubCoordinateEquiv H huv x) (hubCoordinateEquiv H huv y) ↔ hubChartAdj H x y := by
  rcases x with x | ⟨C,i⟩ <;> rcases y with y | ⟨D,j⟩
  · fin_cases x <;> fin_cases y <;>
      simp [hubCoordinateEquiv,hubSumEquiv,hubSumMap,hubChartAdj,G.adj_comm]
  · fin_cases x
    · exact (H.at_left D j)
    · exact (H.at_right D j)
  · fin_cases y
    · exact (G.adj_comm _ _).trans (H.at_left C i)
    · exact (G.adj_comm _ _).trans (H.at_right C i)
  · by_cases he : C=D
    · subst D
      change C.toSimpleGraph.Adj (H.coord C i) (H.coord C j) ↔ _
      simpa [hubChartAdj] using H.internal C i j
    · have hn := different_components_not_adj he (H.coord C i) (H.coord D j)
      simp only [hubCoordinateEquiv_component,hubChartAdj,he,false_and]
      exact iff_false_intro hn

def partitionTwoPredicates {α : Type*} (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀x,P x ∨ Q x) (x : α) : {x // P x ∧ ¬Q x} ⊕ ({x // Q x ∧ ¬P x} ⊕ {x // P x ∧ Q x}) :=
  if hp : P x then if hq : Q x then .inr (.inr ⟨x,hp,hq⟩) else .inl ⟨x,hp,hq⟩
  else .inr (.inl ⟨x,(h x).resolve_left hp,hp⟩)

def unpartitionTwoPredicates {α : Type*} {P Q : α → Prop} :
    {x // P x ∧ ¬Q x} ⊕ ({x // Q x ∧ ¬P x} ⊕ {x // P x ∧ Q x}) → α
  | .inl x => x.val
  | .inr (.inl x) => x.val
  | .inr (.inr x) => x.val

def partitionTwoEquiv {α : Type*} (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀x,P x ∨ Q x) : α ≃ {x // P x ∧ ¬Q x} ⊕ ({x // Q x ∧ ¬P x} ⊕ {x // P x ∧ Q x}) where
  toFun := partitionTwoPredicates P Q h
  invFun := unpartitionTwoPredicates
  left_inv x := by simp only [partitionTwoPredicates]; split_ifs <;> rfl
  right_inv x := by
    rcases x with x | x
    · simp [partitionTwoPredicates,unpartitionTwoPredicates,x.property.1,x.property.2]
    · rcases x with x | x
      · simp [partitionTwoPredicates,unpartitionTwoPredicates,x.property.1,x.property.2]
      · simp [partitionTwoPredicates,unpartitionTwoPredicates,x.property.1,x.property.2]

noncomputable def finiteEquivFinOfNatCard {α : Type*} [Finite α] {n : ℕ} (h : Nat.card α=n) : α ≃ Fin n := by
  letI : Fintype α := Fintype.ofFinite α
  exact Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using h)

/-- The entire set of retained components consists of three left arms,
two right arms, and zero or one bridge component. -/
noncomputable def branch43ComponentEquiv {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (ht : G.IsTree) {u v : Fin n} (hb : Math15.Graceful.Branch43 G u v) :
    HubC G u v ≃ Fin 3 ⊕ (Fin 2 ⊕ Fin (if G.Adj u v then 0 else 1)) := by
  classical
  obtain ⟨hl,hr,hb'⟩ := branch43_component_counts ht hb
  exact (partitionTwoEquiv (fun C : HubC G u v => ComponentAttached C u)
    (fun C => ComponentAttached C v) (component_attached_either ht.isConnected u v)).trans
      (Equiv.sumCongr (finiteEquivFinOfNatCard hl)
        (Equiv.sumCongr (finiteEquivFinOfNatCard hr) (finiteEquivFinOfNatCard hb')))

end Math15Source10
#print axioms Math15Source10.hub_chart_adj_iff
#print axioms Math15Source10.branch43ComponentEquiv
