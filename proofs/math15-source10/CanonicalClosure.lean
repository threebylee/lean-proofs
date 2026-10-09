import SixChartEdges
import SixLabeling

namespace Math15Source10
open SimpleGraph

theorem six_order_selection (L : Fin 3 → ℕ) (hL : ∀i,1≤L i) (e f : ℕ) :
    ∃σ : Equiv.Perm (Fin 3),
      (e≠2 ∨ f≠2) ∧ L (σ 0)≤L (σ 1) ∧ L (σ 1)≤L (σ 2) ∨
      e=2 ∧ f=2 ∧ ExceptionalArmCase (L (σ 0)) (L (σ 1)) (L (σ 2)) := by
  by_cases h : e=2 ∧ f=2
  · obtain ⟨σ,hσ⟩ := exceptional_arm_case_selection L hL
    exact ⟨σ,Or.inr ⟨h.1,h.2,hσ⟩⟩
  · obtain ⟨σ,hσ⟩ := order_three_arms L
    exact ⟨σ,Or.inl ⟨by omega,hσ⟩⟩

/-- Every tree with branching degrees 4 and 3 is graceful. The proof derives
its six-path presentation from the tree and covers every positive arm length. -/
theorem source10_verified : Math15.Graceful.Target10 := by
  classical
  intro n G ht hbranch
  obtain ⟨u,v,hb⟩ := hbranch
  obtain ⟨H⟩ := branch43_has_coordinates ht hb
  obtain ⟨T⟩ := terminalChoice_exists ht hb
  obtain ⟨B⟩ := bridgeChart_exists ht hb.1 H
  let L : Fin 3 → ℕ := fun i => H.length (T.leftC i)+1
  let e := H.length (T.rightC 0)+1
  let f := H.length (T.rightC 1)+1
  obtain ⟨σ,hσ⟩ := six_order_selection L (by intro i; dsimp [L]; omega) e f
  let T' := T.permute σ
  have hcase :
      ((H.length (T'.rightC 0)+1)≠2 ∨ (H.length (T'.rightC 1)+1)≠2) ∧
        (H.length (T'.leftC 0)+1)≤(H.length (T'.leftC 1)+1) ∧
        (H.length (T'.leftC 1)+1)≤(H.length (T'.leftC 2)+1) ∨
      (H.length (T'.rightC 0)+1)=2 ∧ (H.length (T'.rightC 1)+1)=2 ∧
        ExceptionalArmCase (H.length (T'.leftC 0)+1) (H.length (T'.leftC 1)+1)
          (H.length (T'.leftC 2)+1) := by
    exact hσ
  obtain ⟨F,hF⟩ := six_labeling_cases
    (H.length (T'.leftC 0)+1) (H.length (T'.leftC 1)+1) (H.length (T'.leftC 2)+1)
    B.length (H.length (T'.rightC 0)+1) (H.length (T'.rightC 1)+1)
    (by omega) (by omega) (by omega) B.positive (by omega) (by omega) hcase
  let ev := (Equiv.ofBijective (sixChartMap H T' B) (sixChartMap_bijective H T' B)).trans
    (hubCoordinateEquiv H hb.1)
  apply graceful_of_tree_embedding hF G ht ev
  intro i
  exact (hub_chart_adj_iff H hb.1 _ _).mpr (sixChartMap_edges H T' B i)

theorem source12_verified : Math15.Graceful.Target12 :=
  Math15.Graceful.target10_implies12 source10_verified

end Math15Source10
#print Math15Source10.source10_verified
#print axioms Math15Source10.source10_verified
#print axioms Math15Source10.source12_verified
