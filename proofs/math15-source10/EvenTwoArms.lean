import CaterpillarCore
import SingletonLift
import CanonicalBridge
import OddTwoArms

namespace Math15Source10

theorem complete_reflect {V E : Type*} {m : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) : Complete m (fun v => m-f v) ends := by
  rcases h with ⟨hi,hb,hs,hp,hu⟩
  have hd : ∀ e, Nat.dist (m-f (ends e).1) (m-f (ends e).2) =
      Nat.dist (f (ends e).1) (f (ends e).2) := by
    intro e
    have := hb (ends e).1
    have := hb (ends e).2
    simp only [Nat.dist]
    omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro v w he
    dsimp only at he
    have := hb v
    have := hb w
    exact hi (by omega)
  · intro v; dsimp only; omega
  · intro k hk
    obtain ⟨v,hv⟩ := hs (m-k) (by omega)
    exact ⟨v,by dsimp only; omega⟩
  · intro e; simpa only [hd] using hp e
  · intro d h1 h2
    simpa only [hd] using hu d h1 h2

def coreRoot (t : ℕ) : CoreV t := .inl ⟨0,by omega⟩

def evenSide (t : ℕ) : CoreE t → Bool
  | .inl i => decide (i.val % 2 = 1)
  | .inr j => if j.val < 3 then false else decide (t % 2 = 1)

theorem evenSide_root (t : ℕ) (ht : 1 ≤ t) (e : CoreE t) :
    (coreEnds t e).1 = coreRoot t ∨ (coreEnds t e).2 = coreRoot t →
      evenSide t e = false := by
  intro he
  cases e with
  | inl i =>
    simp only [coreEnds,coreRoot,Sum.inl.injEq,Fin.mk.injEq] at he
    simp only [evenSide]
    have : i.val = 0 := by omega
    simp [this]
  | inr j =>
    by_cases hj : j.val < 3
    · simp [evenSide,hj]
    · simp [coreEnds,coreRoot,hj,Fin.ext_iff] at he
      omega

def evenEnds (t : ℕ) (ht : 1 ≤ t) := thinEnds (coreEnds t) (evenSide t) (evenSide_root t ht)
def evenLabel (t : ℕ) := thinLabel (r:=coreRoot t) (t+5) (fun v => t+5-coreLabel t v)

theorem even_complete (t : ℕ) (ht : 1 ≤ t) :
    Complete (2*t+10) (evenLabel t) (evenEnds t ht) := by
  have hroot : t+5-coreLabel t (coreRoot t) = t+5 := by simp [coreRoot,coreLabel]
  convert singleton_lift (complete_reflect (core_complete t)) (by omega)
    (coreRoot t) hroot (evenSide t) (evenSide_root t ht) using 1 <;>
    simp [evenLabel,evenEnds] <;> omega

/-- The exact challenge IsGraceful predicate for the two explicit families.
The graph is represented by its endpoint labels; no target theorem is assumed. -/
theorem odd_graph_graceful (t : ℕ) :
    Math15.Graceful.IsGraceful (certificateGraph (odd_complete t)) :=
  certificateGraph_graceful (odd_complete t)

theorem even_graph_graceful (t : ℕ) (ht : 1 ≤ t) :
    Math15.Graceful.IsGraceful (certificateGraph (even_complete t ht)) := by
  classical
  exact certificateGraph_graceful (even_complete t ht)

end Math15Source10
#print axioms Math15Source10.even_complete
#print axioms Math15Source10.odd_graph_graceful
#print axioms Math15Source10.even_graph_graceful
