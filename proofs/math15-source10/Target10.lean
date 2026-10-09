import CanonicalBridge

-- Exact Source 10 and Source 12 target definitions.
-- This file states the full target; it does not assert that it has been proved.
namespace Math15.Graceful
open Finset

noncomputable def degree {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : ℕ := by
  classical
  exact ((univ : Finset (Fin n)).filter (G.Adj u)).card

def Branch43 {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Prop :=
  u ≠ v ∧ degree G u = 4 ∧ degree G v = 3 ∧
  ∀ w, w ≠ u → w ≠ v → degree G w ≤ 2

/-- The two arms at v have exactly two edges. Freshness is explicit. -/
def TwoLengthTwoArms {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∃ x₁ x₂ y₁ y₂ : Fin n,
    ({v, x₁, x₂, y₁, y₂} : Finset (Fin n)).card = 5 ∧
    G.Adj v x₁ ∧ G.Adj x₁ y₁ ∧ G.Adj v x₂ ∧ G.Adj x₂ y₂ ∧
    degree G x₁ = 2 ∧ degree G x₂ = 2 ∧ degree G y₁ = 1 ∧ degree G y₂ = 1

def Target10 : Prop := ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
  G.IsTree → (∃ u v, Branch43 G u v) → IsGraceful G

def Target12 : Prop := ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
  G.IsTree → (∃ u v, Branch43 G u v ∧ TwoLengthTwoArms G v) → IsGraceful G

theorem target10_implies12 (h : Target10) : Target12 := by
  intro n G ht hbranch
  obtain ⟨u, v, huv, _⟩ := hbranch
  exact h n G ht ⟨u, v, huv⟩

end Math15.Graceful
#print Math15.Graceful.Target10
#print axioms Math15.Graceful.target10_implies12
