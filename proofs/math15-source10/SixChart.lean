import SixModel
import TerminalChoice
import BridgeChart

namespace Math15Source10
open SimpleGraph

abbrev ChartArms {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (T : TerminalChoice G u v) :=
  ArmsV (H.length (T.leftC 0)+1) (H.length (T.leftC 1)+1) (H.length (T.leftC 2)+1)
    (H.length (T.rightC 0)+1) (H.length (T.rightC 1)+1)

def terminalMap {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (T : TerminalChoice G u v) : ChartArms H T → HubChartV H
  | .inl i => .inr ⟨T.leftC 0,i⟩
  | .inr (.inl i) => .inr ⟨T.leftC 1,i⟩
  | .inr (.inr (.inl i)) => .inr ⟨T.leftC 2,i⟩
  | .inr (.inr (.inr (.inl i))) => .inr ⟨T.rightC 0,i⟩
  | .inr (.inr (.inr (.inr i))) => .inr ⟨T.rightC 1,i⟩

theorem terminalMap_injective {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (T : TerminalChoice G u v) : Function.Injective (terminalMap H T) := by
  intro x y he
  rcases x with x | x | x | x | x <;> rcases y with y | y | y | y | y <;>
    simp_all [terminalMap,Sigma.mk.inj_iff]

theorem terminalMap_bridge_disjoint {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (T : TerminalChoice G u v) (B : BridgeChart H)
    (i : Fin (B.length+1)) (x : ChartArms H T) : B.vertex i≠terminalMap H T x := by
  rcases x with x | x | x | x | x
  · exact B.disjoint _ (Or.inl (T.left 0).property) i x
  · exact B.disjoint _ (Or.inl (T.left 1).property) i x
  · exact B.disjoint _ (Or.inl (T.left 2).property) i x
  · exact B.disjoint _ (Or.inr (T.right 0).property) i x
  · exact B.disjoint _ (Or.inr (T.right 1).property) i x

theorem terminalMap_left_cover {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (T : TerminalChoice G u v) (C : HubC G u v)
    (hc : ComponentAttached C u ∧ ¬ComponentAttached C v) (j : Fin (H.length C+1)) :
    ∃x,terminalMap H T x=.inr ⟨C,j⟩ := by
  obtain ⟨i,hi⟩ := T.left.surjective ⟨C,hc⟩
  have hC : T.leftC i=C := congrArg Subtype.val hi
  fin_cases i
  · subst C; exact ⟨.inl j,rfl⟩
  · subst C; exact ⟨.inr (.inl j),rfl⟩
  · subst C; exact ⟨.inr (.inr (.inl j)),rfl⟩

theorem terminalMap_right_cover {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (T : TerminalChoice G u v) (C : HubC G u v)
    (hc : ComponentAttached C v ∧ ¬ComponentAttached C u) (j : Fin (H.length C+1)) :
    ∃x,terminalMap H T x=.inr ⟨C,j⟩ := by
  obtain ⟨i,hi⟩ := T.right.surjective ⟨C,hc⟩
  have hC : T.rightC i=C := congrArg Subtype.val hi
  fin_cases i
  · subst C; exact ⟨.inr (.inr (.inr (.inl j))),rfl⟩
  · subst C; exact ⟨.inr (.inr (.inr (.inr j))),rfl⟩

def sixChartMap {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (T : TerminalChoice G u v) (B : BridgeChart H) :
    (Fin (B.length+1) ⊕ ChartArms H T) → HubChartV H := Sum.elim B.vertex (terminalMap H T)

theorem sixChartMap_bijective {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (T : TerminalChoice G u v) (B : BridgeChart H) :
    Function.Bijective (sixChartMap H T B) := by
  classical
  constructor
  · intro x y he
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (B.injective he)
    · exact (terminalMap_bridge_disjoint H T B x y he).elim
    · exact (terminalMap_bridge_disjoint H T B y x he.symm).elim
    · exact congrArg Sum.inr (terminalMap_injective H T he)
  · intro x
    rcases x with i | ⟨C,j⟩
    · fin_cases i
      · exact ⟨.inl 0,B.first⟩
      · exact ⟨.inl ⟨B.length,by omega⟩,B.last⟩
    · by_cases hu : ComponentAttached C u
      · by_cases hv : ComponentAttached C v
        · obtain ⟨i,hi⟩ := B.cover C hu hv j
          exact ⟨.inl i,hi⟩
        · obtain ⟨i,hi⟩ := terminalMap_left_cover H T C ⟨hu,hv⟩ j
          exact ⟨.inr i,hi⟩
      · have hv : ComponentAttached C v := by
          cases h : H.atU C
          · exact coordinate_false_attached H C h
          · exact (hu (coordinate_true_attached H C h)).elim
        obtain ⟨i,hi⟩ := terminalMap_right_cover H T C ⟨hv,hu⟩ j
        exact ⟨.inr i,hi⟩

end Math15Source10
#print axioms Math15Source10.sixChartMap_bijective
