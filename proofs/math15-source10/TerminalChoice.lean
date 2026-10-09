import HubChart

namespace Math15Source10
open SimpleGraph

structure TerminalChoice {V : Type*} (G : SimpleGraph V) (u v : V) where
  left : Fin 3 ≃ {C : HubC G u v // ComponentAttached C u ∧ ¬ComponentAttached C v}
  right : Fin 2 ≃ {C : HubC G u v // ComponentAttached C v ∧ ¬ComponentAttached C u}

def TerminalChoice.leftC {V : Type*} {G : SimpleGraph V} {u v : V}
    (T : TerminalChoice G u v) (i : Fin 3) : HubC G u v := (T.left i).val
def TerminalChoice.rightC {V : Type*} {G : SimpleGraph V} {u v : V}
    (T : TerminalChoice G u v) (i : Fin 2) : HubC G u v := (T.right i).val

theorem TerminalChoice.leftC_injective {V : Type*} {G : SimpleGraph V} {u v : V}
    (T : TerminalChoice G u v) : Function.Injective T.leftC := by
  intro i j he
  exact T.left.injective (Subtype.ext he)
theorem TerminalChoice.rightC_injective {V : Type*} {G : SimpleGraph V} {u v : V}
    (T : TerminalChoice G u v) : Function.Injective T.rightC := by
  intro i j he
  exact T.right.injective (Subtype.ext he)
@[simp] theorem TerminalChoice.leftC_ne_rightC {V : Type*} {G : SimpleGraph V} {u v : V}
    (T : TerminalChoice G u v) (i : Fin 3) (j : Fin 2) : T.leftC i≠T.rightC j := by
  intro he
  have h1 : ¬ComponentAttached (T.leftC i) v := (T.left i).property.2
  have h2 : ComponentAttached (T.rightC j) v := (T.right j).property.1
  exact h1 (he ▸ h2)

@[simp] theorem TerminalChoice.leftC_eq_iff {V : Type*} {G : SimpleGraph V} {u v : V}
    (T : TerminalChoice G u v) (i j : Fin 3) : T.leftC i=T.leftC j ↔ i=j :=
  T.leftC_injective.eq_iff
@[simp] theorem TerminalChoice.rightC_eq_iff {V : Type*} {G : SimpleGraph V} {u v : V}
    (T : TerminalChoice G u v) (i j : Fin 2) : T.rightC i=T.rightC j ↔ i=j :=
  T.rightC_injective.eq_iff
@[simp] theorem TerminalChoice.rightC_ne_leftC {V : Type*} {G : SimpleGraph V} {u v : V}
    (T : TerminalChoice G u v) (i : Fin 2) (j : Fin 3) : T.rightC i≠T.leftC j :=
  (T.leftC_ne_rightC j i).symm

def TerminalChoice.permute {V : Type*} {G : SimpleGraph V} {u v : V}
    (T : TerminalChoice G u v) (σ : Equiv.Perm (Fin 3)) : TerminalChoice G u v :=
  ⟨σ.trans T.left,T.right⟩

theorem terminalChoice_exists {n : ℕ} {G : SimpleGraph (Fin n)} (ht : G.IsTree)
    {u v : Fin n} (hb : Math15.Graceful.Branch43 G u v) : Nonempty (TerminalChoice G u v) := by
  classical
  obtain ⟨hl,hr,_⟩ := branch43_component_counts ht hb
  exact ⟨⟨(finiteEquivFinOfNatCard hl).symm,(finiteEquivFinOfNatCard hr).symm⟩⟩

end Math15Source10
#print axioms Math15Source10.terminalChoice_exists
