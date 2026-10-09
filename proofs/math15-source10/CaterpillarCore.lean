import MatchingLift

namespace Math15Source10

abbrev CoreV (t : ℕ) := Fin (t+1) ⊕ Fin 5
abbrev CoreE (t : ℕ) := Fin t ⊕ Fin 5

/-- A path of length t, with three leaves at its first vertex and two at
its last. For t=0 the two path endpoints coincide, giving a five-leaf star. -/
def coreEnds (t : ℕ) : CoreE t → CoreV t × CoreV t
  | .inl i => (.inl ⟨i.val, by omega⟩, .inl ⟨i.val+1, by omega⟩)
  | .inr j => (if j.val < 3 then .inl ⟨0, by omega⟩ else .inl ⟨t, by omega⟩,
      .inr j)

def coreLabel (t : ℕ) : CoreV t → ℕ
  | .inl i => if i.val % 2 = 0 then i.val/2 else t+2-i.val/2
  | .inr j => if j.val < 3 then t+5-j.val else t/2+j.val-2

def coreWeight (t : ℕ) : CoreE t → ℕ
  | .inl i => t+2-i.val
  | .inr j => if j.val < 3 then t+5-j.val else
      if t%2=0 then j.val-2 else 5-j.val

theorem coreLabel_bound (t : ℕ) (v : CoreV t) : coreLabel t v ≤ t+5 := by
  cases v <;> simp only [coreLabel] <;> split_ifs <;> omega

theorem coreLabel_injective (t : ℕ) : Function.Injective (coreLabel t) := by
  intro v w he
  cases v with
  | inl i =>
    cases w with
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [coreLabel] at he
      split_ifs at he <;> omega
    | inr j =>
      simp only [coreLabel] at he
      split_ifs at he <;> omega
  | inr i =>
    cases w with
    | inl j =>
      simp only [coreLabel] at he
      split_ifs at he <;> omega
    | inr j =>
      apply congrArg Sum.inr
      apply Fin.ext
      simp only [coreLabel] at he
      split_ifs at he <;> omega

theorem coreLabel_onto (t k : ℕ) (hk : k ≤ t+5) : ∃ v, coreLabel t v = k := by
  let f : CoreV t → Fin (t+6) := fun v => ⟨coreLabel t v, by have := coreLabel_bound t v; omega⟩
  have hi : Function.Injective f := by
    intro v w he
    apply coreLabel_injective t
    exact congrArg Fin.val he
  have hs : Function.Surjective f := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective f hi hn
    simp only [CoreV, Fintype.card_sum, Fintype.card_fin] at hlt
    omega
  obtain ⟨v,hv⟩ := hs ⟨k, by omega⟩
  exact ⟨v, congrArg Fin.val hv⟩

theorem core_dist (t : ℕ) (e : CoreE t) :
    Nat.dist (coreLabel t (coreEnds t e).1) (coreLabel t (coreEnds t e).2) =
      coreWeight t e := by
  cases e with
  | inl i =>
    simp only [coreEnds, coreLabel, coreWeight, Nat.dist]
    split_ifs <;> omega
  | inr j =>
    by_cases hj : j.val < 3
    · simp [coreEnds, coreLabel, coreWeight, hj, Nat.dist]
    · simp only [coreEnds, hj, ↓reduceIte, coreLabel, coreWeight, Nat.dist]
      split_ifs <;> omega

theorem coreWeight_injective (t : ℕ) : Function.Injective (coreWeight t) := by
  intro e g he
  cases e with
  | inl i =>
    cases g with
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [coreWeight] at he
      omega
    | inr j =>
      simp only [coreWeight] at he
      split_ifs at he <;> omega
  | inr i =>
    cases g with
    | inl j =>
      simp only [coreWeight] at he
      split_ifs at he <;> omega
    | inr j =>
      apply congrArg Sum.inr
      apply Fin.ext
      simp only [coreWeight] at he
      split_ifs at he <;> omega

theorem coreWeight_pos (t : ℕ) (e : CoreE t) : 0 < coreWeight t e := by
  cases e <;> simp only [coreWeight] <;> (try split_ifs) <;> omega

theorem coreWeight_onto (t d : ℕ) (hd : 1 ≤ d) (hm : d ≤ t+5) :
    ∃ e, coreWeight t e = d := by
  by_cases hsmall : d ≤ 2
  · by_cases ht : t%2=0
    · refine ⟨.inr ⟨d+2, by omega⟩, ?_⟩
      simp [coreWeight, ht, show ¬ d+2<3 by omega]
    · refine ⟨.inr ⟨5-d, by omega⟩, ?_⟩
      simp [coreWeight, ht, show ¬ 5-d<3 by omega]
      omega
  · by_cases hmid : d ≤ t+2
    · refine ⟨.inl ⟨t+2-d, by omega⟩, ?_⟩
      simp only [coreWeight]
      omega
    · refine ⟨.inr ⟨t+5-d, by omega⟩, ?_⟩
      simp [coreWeight, show t+5-d<3 by omega]
      omega

/-- Unbounded graceful caterpillar certificate used as the contree of the
five-length-two-arm family. -/
theorem core_complete (t : ℕ) : Complete (t+5) (coreLabel t) (coreEnds t) := by
  refine ⟨coreLabel_injective t, coreLabel_bound t, coreLabel_onto t, ?_, ?_⟩
  · intro e
    rw [core_dist]
    exact coreWeight_pos t e
  · intro d hd hm
    obtain ⟨e,he⟩ := coreWeight_onto t d hd hm
    refine ⟨e, ?_, ?_⟩
    · dsimp only
      rw [core_dist, he]
    · intro z hz
      apply coreWeight_injective t
      rw [core_dist] at hz
      exact hz.trans he.symm

end Math15Source10

#print axioms Math15Source10.core_complete
