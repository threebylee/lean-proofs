import Mathlib.Tactic
import Mathlib.Data.Nat.Dist

namespace Math15Source10

/-- A graceful certificate with each edge represented exactly once. The
surjectivity field is explicit so that matching edges cover every odd weight. -/
def Complete {V E : Type*} (m : ℕ) (f : V → ℕ) (ends : E → V × V) : Prop :=
  Function.Injective f ∧ (∀ v, f v ≤ m) ∧
  (∀ k, k ≤ m → ∃ v, f v = k) ∧
  (∀ e, 0 < Nat.dist (f (ends e).1) (f (ends e).2)) ∧
  ∀ d, 1 ≤ d → d ≤ m → ∃! e, Nat.dist (f (ends e).1) (f (ends e).2) = d

def pairLabel {V : Type*} (m : ℕ) (f : V → ℕ) (v : V × Bool) : ℕ :=
  if v.2 then 2*m+1-2*f v.1 else 2*f v.1

def pairEnds {V E : Type*} (ends : E → V × V) (side : E → Bool) :
    V ⊕ E → (V × Bool) × (V × Bool)
  | .inl v => ((v,false),(v,true))
  | .inr e => (((ends e).1,side e),((ends e).2,side e))

theorem pair_cross {V E : Type*} {m : ℕ} {f : V → ℕ}
    (hb : ∀ v, f v ≤ m) (ends : E → V × V) (side : E → Bool) (e : E) :
    Nat.dist (pairLabel m f (pairEnds ends side (.inr e)).1)
      (pairLabel m f (pairEnds ends side (.inr e)).2) =
      2 * Nat.dist (f (ends e).1) (f (ends e).2) := by
  have h1 := hb (ends e).1
  have h2 := hb (ends e).2
  cases hs : side e <;> simp [pairEnds, pairLabel, hs, Nat.dist] <;> omega

theorem pair_matching {V E : Type*} (m : ℕ) (f : V → ℕ)
    (ends : E → V × V) (side : E → Bool) (v : V) :
    Nat.dist (pairLabel m f (pairEnds ends side (.inl v)).1)
      (pairLabel m f (pairEnds ends side (.inl v)).2) =
      Nat.dist (2*f v) (2*m+1-2*f v) := by
  simp [pairEnds, pairLabel]

theorem matching_odd {m a : ℕ} (ha : a ≤ m) :
    Nat.dist (2*a) (2*m+1-2*a) % 2 = 1 := by
  simp only [Nat.dist]
  omega

theorem matching_injective {m a b : ℕ} (ha : a ≤ m) (hb : b ≤ m)
    (he : Nat.dist (2*a) (2*m+1-2*a) = Nat.dist (2*b) (2*m+1-2*b)) :
    a = b := by
  simp only [Nat.dist] at he
  omega

theorem matching_onto {m d : ℕ} (hd : d ≤ 2*m+1) (ho : d % 2 = 1) :
    ∃ a, a ≤ m ∧ Nat.dist (2*a) (2*m+1-2*a) = d := by
  by_cases hp : (m - d/2) % 2 = 0
  · refine ⟨(m-d/2)/2, ?_, ?_⟩ <;> (try simp only [Nat.dist]) <;> omega
  · refine ⟨(m+d/2+1)/2, ?_, ?_⟩ <;> (try simp only [Nat.dist]) <;> omega

/-- The generalized matching/Delta lift. Each old edge may independently
choose which of the two corresponding endpoints it joins. -/
theorem matching_lift {V E : Type*} {m : ℕ} {f : V → ℕ}
    {ends : E → V × V} (h : Complete m f ends) (side : E → Bool) :
    Complete (2*m+1) (pairLabel m f) (pairEnds ends side) := by
  rcases h with ⟨hi,hb,hs,hp,hu⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨v,b⟩ ⟨w,c⟩ he
    have hv := hb v
    have hw := hb w
    cases b <;> cases c <;> simp only [pairLabel, Bool.false_eq_true, ↓reduceIte] at he
    · have : v = w := hi (by omega)
      subst w
      rfl
    · omega
    · omega
    · have : v = w := hi (by omega)
      subst w
      rfl
  · rintro ⟨v,b⟩
    have := hb v
    cases b <;> simp [pairLabel] <;> omega
  · intro k hk
    by_cases he : k % 2 = 0
    · obtain ⟨v,hv⟩ := hs (k/2) (by omega)
      refine ⟨(v,false), ?_⟩
      simp [pairLabel,hv]
      omega
    · obtain ⟨v,hv⟩ := hs ((2*m+1-k)/2) (by omega)
      refine ⟨(v,true), ?_⟩
      simp [pairLabel,hv]
      omega
  · intro e
    cases e with
    | inl v =>
      rw [pair_matching]
      have := matching_odd (hb v)
      omega
    | inr e =>
      rw [pair_cross hb]
      have := hp e
      omega
  · intro d hd hdm
    by_cases he : d % 2 = 0
    · obtain ⟨e,heq,heuniq⟩ := hu (d/2) (by omega) (by omega)
      refine ⟨.inr e, ?_, ?_⟩
      · dsimp only
        rw [pair_cross hb, heq]
        omega
      · intro z hz
        cases z with
        | inl v =>
          rw [pair_matching] at hz
          have := matching_odd (hb v)
          omega
        | inr z =>
          rw [pair_cross hb] at hz
          exact congrArg Sum.inr (heuniq z (by omega))
    · have hod : d % 2 = 1 := by omega
      obtain ⟨a,ha,had⟩ := matching_onto hdm hod
      obtain ⟨v,hv⟩ := hs a ha
      refine ⟨.inl v, ?_, ?_⟩
      · dsimp only
        rw [pair_matching, hv]
        exact had
      · intro z hz
        cases z with
        | inl w =>
          rw [pair_matching] at hz
          apply congrArg Sum.inl
          apply hi
          apply matching_injective (hb w) (hb v)
          simpa [hv,had] using hz
        | inr e =>
          rw [pair_cross hb] at hz
          omega

end Math15Source10

#print axioms Math15Source10.matching_lift
