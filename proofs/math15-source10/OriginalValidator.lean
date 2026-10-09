import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic
import Mathlib.Data.Nat.Dist

namespace Math15Source10.OriginalValidator
open Finset

/-- Every edge difference occurs once, using both injectivity and complete coverage.
The `u < v` orientation makes unordered edges count exactly once. -/
noncomputable def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)).card
noncomputable def degree {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : ℕ := by
  classical
  exact ((univ : Finset (Fin n)).filter (G.Adj u)).card

def IsGraceful {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → ℕ, Function.Injective f ∧
    (∀ v, f v ≤ edgeCount G) ∧
    (∀ d, 1 ≤ d → d ≤ edgeCount G →
      ∃! e : Fin n × Fin n, e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ Nat.dist (f e.1) (f e.2) = d)

def Branch43 {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Prop :=
  u ≠ v ∧ degree G u = 4 ∧ degree G v = 3 ∧
  ∀ w, w ≠ u → w ≠ v → degree G w ≤ 2

def Branch333 {n : ℕ} (G : SimpleGraph (Fin n)) (u v w : Fin n) : Prop :=
  u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ degree G u = 3 ∧ degree G v = 3 ∧ degree G w = 3 ∧
  ∀ x, x ≠ u → x ≠ v → x ≠ w → degree G x ≤ 2

/-- The two arms at v have exactly two edges. Freshness is explicit. -/
def TwoLengthTwoArms {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∃ x₁ x₂ y₁ y₂ : Fin n,
    ({v, x₁, x₂, y₁, y₂} : Finset (Fin n)).card = 5 ∧
    G.Adj v x₁ ∧ G.Adj x₁ y₁ ∧ G.Adj v x₂ ∧ G.Adj x₂ y₂ ∧
    degree G x₁ = 2 ∧ degree G x₂ = 2 ∧ degree G y₁ = 1 ∧ degree G y₂ = 1

def Target10 : Prop := ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
  G.IsTree → (∃ u v, Branch43 G u v) → IsGraceful G

def Target11 : Prop := ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
  G.IsTree → (∃ u v w, Branch333 G u v w) → IsGraceful G

def Target12 : Prop := ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
  G.IsTree → (∃ u v, Branch43 G u v ∧ TwoLengthTwoArms G v) → IsGraceful G

theorem target10_implies12 (h : Target10) : Target12 := by
  intro n G ht hbranch
  obtain ⟨u, v, huv, _⟩ := hbranch
  exact h n G ht ⟨u, v, huv⟩

end Math15Source10.OriginalValidator
