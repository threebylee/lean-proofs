import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

noncomputable section
namespace Math15.LonelyRunner
open Finset Set
abbrev Time := AddCircle (1 : ℝ)
/-- Circle norm is exactly distance to the nearest integer, by `AddCircle.norm_eq`. -/
def distance (t : Time) : ℝ := ‖t‖
def Positive (V : Finset ℕ) : Prop := ∀ v ∈ V, 0 < v
def Primitive (V : Finset ℕ) : Prop := V.gcd id = 1

def score (V : Finset ℕ) (t : Time) : ℝ :=
  if h : V.Nonempty then V.inf' h (fun v => distance (v • t)) else 0

def ML (V : Finset ℕ) : ℝ := sSup (Set.range (score V))

theorem score_continuous (V : Finset ℕ) : Continuous (score V) := by
  unfold score
  split_ifs with h
  · apply Continuous.finset_inf'_apply
    intro v hv
    unfold distance
    fun_prop
  · exact continuous_const

/-- This supremum is an attained maximum; no rational-time completeness is assumed. -/
theorem ML_attained (V : Finset ℕ) : ∃ t : Time, score V t = ML V := by
  obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (score_continuous V).continuousOn
  refine ⟨t, le_antisymm ?_ ?_⟩
  · exact le_csSup ⟨score V t, by rintro _ ⟨s, rfl⟩; exact ht (Set.mem_univ s)⟩ ⟨t, rfl⟩
  · exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨s, rfl⟩; exact ht (Set.mem_univ s))

theorem ML_le_half (V : Finset ℕ) : ML V ≤ 1 / 2 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨t, rfl⟩
  by_cases h : V.Nonempty
  · simp only [score, dif_pos h]
    obtain ⟨v, hv⟩ := h
    exact (Finset.inf'_le (fun v => distance (v • t)) hv).trans (by
      simpa [distance] using AddCircle.norm_le_half_period (1 : ℝ) (by norm_num) (x := v • t))
  · simp [score, h]

/-- Two deleted upper-half speeds can match in either order. -/
def ReplacementCondition (n r w : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ w = m * r ∧
    ∀ b : ℕ, n - r ≤ b → b < m * (n - r) → 1 < Nat.gcd r b

def modified (n r₁ r₂ w₁ w₂ : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n - 1) \ {r₁, r₂}) ∪ {w₁, w₂}

def Target04 : Prop := ∀ n r₁ r₂ w₁ w₂ : ℕ,
  3 ≤ n → 1 ≤ r₁ → r₁ < n → 1 ≤ r₂ → r₂ < n → r₁ ≠ r₂ →
  n - 1 < 2 * r₁ → n - 1 < 2 * r₂ → n ≤ w₁ → n ≤ w₂ → w₁ ≠ w₂ →
  ML (modified n r₁ r₂ w₁ w₂) = 1 / (n : ℝ) →
  (ReplacementCondition n r₁ w₁ ∧ ReplacementCondition n r₂ w₂) ∨
  (ReplacementCondition n r₁ w₂ ∧ ReplacementCondition n r₂ w₁)

def Target05 : Prop := ∀ V : Finset ℕ,
  Positive V → V.card = 4 → Primitive V →
  (∀ u ∈ V, ∀ v ∈ V, u ≠ v → Nat.gcd u v ≤ 2) →
  (1 / 4 : ℝ) ≤ ML V ∨ ∃ s k : ℕ, 1 ≤ k ∧ k ≤ 4 ∧ k ≤ s ∧
    ML V = (s : ℝ) / (4 * (s : ℝ) + k)

def Target06 : Prop := ∀ (V : Finset ℕ) (p q : ℕ),
  Positive V → V.card = 6 → Primitive V → 0 < p → 0 < q → Nat.Coprime p q →
  ML V = (p : ℝ) / q → 6 * p < q → ∀ v ∈ V, v < 3 * q

end Math15.LonelyRunner
