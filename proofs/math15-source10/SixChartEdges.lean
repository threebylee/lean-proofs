import SixChart

namespace Math15Source10
open SimpleGraph

theorem left_arm_chart_edges {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v)
    (hc : ComponentAttached C u ∧ ¬ComponentAttached C v)
    (i : Fin (H.length C+1)) :
    hubChartAdj H (armEnds (.inl 0) (fun j => (.inr ⟨C,j⟩ : HubChartV H)) i).1
      (armEnds (.inl 0) (fun j => (.inr ⟨C,j⟩ : HubChartV H)) i).2 := by
  have hb := left_only_coordinate_orientation H C hc.2
  by_cases hi : i.val=0
  · simp [armEnds,hi,hubChartAdj,hb]
  · simp [armEnds,hi,hubChartAdj]
    omega

theorem right_arm_chart_edges {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v)
    (hc : ComponentAttached C v ∧ ¬ComponentAttached C u)
    (i : Fin (H.length C+1)) :
    hubChartAdj H (armEnds (.inl 1) (fun j => (.inr ⟨C,j⟩ : HubChartV H)) i).1
      (armEnds (.inl 1) (fun j => (.inr ⟨C,j⟩ : HubChartV H)) i).2 := by
  have hb := right_only_coordinate_orientation H C hc.2
  by_cases hi : i.val=0
  · simp [armEnds,hi,hubChartAdj,hb]
  · simp [armEnds,hi,hubChartAdj]
    omega

theorem sixChartMap_edges {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (T : TerminalChoice G u v) (B : BridgeChart H)
    (i : SixE (H.length (T.leftC 0)+1) (H.length (T.leftC 1)+1) (H.length (T.leftC 2)+1)
      B.length (H.length (T.rightC 0)+1) (H.length (T.rightC 1)+1)) :
    hubChartAdj H
      (sixChartMap H T B (sixEnds _ _ _ _ _ _ i).1)
      (sixChartMap H T B (sixEnds _ _ _ _ _ _ i).2) := by
  rcases i with i | i
  · exact B.edges i
  · rcases i with i | i | i | i | i
    · have h := left_arm_chart_edges H (T.leftC 0) (T.left 0).property i
      by_cases hi : i.val=0 <;> simpa [sixChartMap,sixEnds,armEnds,terminalMap,hi,B.first] using h
    · have h := left_arm_chart_edges H (T.leftC 1) (T.left 1).property i
      by_cases hi : i.val=0 <;> simpa [sixChartMap,sixEnds,armEnds,terminalMap,hi,B.first] using h
    · have h := left_arm_chart_edges H (T.leftC 2) (T.left 2).property i
      by_cases hi : i.val=0 <;> simpa [sixChartMap,sixEnds,armEnds,terminalMap,hi,B.first] using h
    · have h := right_arm_chart_edges H (T.rightC 0) (T.right 0).property i
      by_cases hi : i.val=0 <;> simpa [sixChartMap,sixEnds,armEnds,terminalMap,hi,B.last] using h
    · have h := right_arm_chart_edges H (T.rightC 1) (T.right 1).property i
      by_cases hi : i.val=0 <;> simpa [sixChartMap,sixEnds,armEnds,terminalMap,hi,B.last] using h

end Math15Source10
#print axioms Math15Source10.sixChartMap_edges
