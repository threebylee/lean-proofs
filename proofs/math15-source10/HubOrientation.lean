import HubChart

namespace Math15Source10
open SimpleGraph

theorem coordinate_true_attached {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v) (h : H.atU C=true) :
    ComponentAttached C u := by
  refine ⟨H.coord C 0,?_⟩
  exact (H.at_left C 0).mpr (by simp [h])

theorem coordinate_false_attached {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v) (h : H.atU C=false) :
    ComponentAttached C v := by
  refine ⟨H.coord C 0,?_⟩
  exact (H.at_right C 0).mpr (by simp [h])

theorem left_only_coordinate_orientation {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v) (hv : ¬ComponentAttached C v) :
    H.atU C=true := by
  cases h : H.atU C
  · exact (hv (coordinate_false_attached H C h)).elim
  · rfl

theorem right_only_coordinate_orientation {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v) (hu : ¬ComponentAttached C u) :
    H.atU C=false := by
  cases h : H.atU C
  · rfl
  · exact (hu (coordinate_true_attached H C h)).elim

def orientedBridgeIndex {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v) (i : Fin (H.length C+1)) :
    Fin (H.length C+1) := if H.atU C then i else i.rev

theorem orientedBridgeIndex_involutive {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v) :
    Function.Involutive (orientedBridgeIndex H C) := by
  intro i
  simp only [orientedBridgeIndex]
  cases H.atU C <;> simp

/-- Both bridge attachments are oriented from u to v, including a singleton
component. No positive-length assumption on the retained component is needed. -/
theorem oriented_bridge_endpoints {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v)
    (hu : ComponentAttached C u) (hv : ComponentAttached C v)
    (i : Fin (H.length C+1)) :
    (G.Adj u (componentEmbedding (outsideTwo u v) C
      (H.coord C (orientedBridgeIndex H C i))) ↔ i.val=0) ∧
    (G.Adj v (componentEmbedding (outsideTwo u v) C
      (H.coord C (orientedBridgeIndex H C i))) ↔ i.val=H.length C) := by
  rw [H.at_left,H.at_right]
  cases h : H.atU C
  · simp only [orientedBridgeIndex,h,Bool.false_eq_true,ite_false,hu,hv,true_and,
      Fin.val_rev]
    constructor <;> omega
  · simp [orientedBridgeIndex,h,hu,hv]

theorem oriented_bridge_internal {V : Type*} {G : SimpleGraph V} {u v : V}
    (H : HubCoordinates G u v) (C : HubC G u v)
    (i j : Fin (H.length C+1)) :
    C.toSimpleGraph.Adj (H.coord C (orientedBridgeIndex H C i))
      (H.coord C (orientedBridgeIndex H C j)) ↔
      i.val+1=j.val ∨ j.val+1=i.val := by
  rw [H.internal]
  cases h : H.atU C
  · simp only [orientedBridgeIndex,h,Bool.false_eq_true,ite_false,Fin.val_rev]
    omega
  · simp [orientedBridgeIndex,h]

end Math15Source10
#print axioms Math15Source10.oriented_bridge_endpoints
#print axioms Math15Source10.oriented_bridge_internal
