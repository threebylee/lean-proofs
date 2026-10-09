import MatchingLift

namespace Math15Source10

def Alpha {V E : Type*} (k : ℕ) (f : V → ℕ) (ends : E → V × V) : Prop :=
  ∀ e, (f (ends e).1 ≤ k ∧ k < f (ends e).2) ∨
    (f (ends e).2 ≤ k ∧ k < f (ends e).1)

def tailEnds {V E : Type*} (ends : E → V × V) (r : V) :
    E ⊕ Fin 4 → (V ⊕ Fin 4) × (V ⊕ Fin 4)
  | .inl e => (.inl (ends e).1,.inl (ends e).2)
  | .inr i => (if h : i.val=0 then .inl r else .inr ⟨i.val-1,by omega⟩,.inr i)

def oneTailLabel {V : Type*} (m : ℕ) (f : V → ℕ) : V ⊕ Fin 4 → ℕ
  | .inl v => f v+2
  | .inr i => if i.val=0 then m+4 else if i.val=1 then 0 else if i.val=2 then m+3 else 1

def oneTailWeight (m : ℕ) (i : Fin 4) := if i.val=0 then m+1 else m+5-i.val

theorem oneTail_old {V E : Type*} (m : ℕ) (f : V → ℕ) (ends : E → V × V) (r : V) (e : E) :
    Nat.dist (oneTailLabel m f (tailEnds ends r (.inl e)).1)
      (oneTailLabel m f (tailEnds ends r (.inl e)).2) =
      Nat.dist (f (ends e).1) (f (ends e).2) := by
  simp [tailEnds,oneTailLabel,Nat.dist]

theorem oneTail_new {V E : Type*} (m : ℕ) (f : V → ℕ) (ends : E → V × V) (r : V)
    (hr : f r=1) (i : Fin 4) :
    Nat.dist (oneTailLabel m f (tailEnds ends r (.inr i)).1)
      (oneTailLabel m f (tailEnds ends r (.inr i)).2) = oneTailWeight m i := by
  fin_cases i <;> simp [tailEnds,oneTailLabel,oneTailWeight,hr,Nat.dist] <;> omega

/-- Attach four edges at a vertex labeled one. Translating old labels by two
and using m+4,0,m+3,1 on the tail preserves gracefulness and ends again at one. -/
theorem one_tail_complete {V E : Type*} {m : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (r : V) (hr : f r=1) :
    Complete (m+4) (oneTailLabel m f) (tailEnds ends r) := by
  rcases h with ⟨hi,hb,hs,hp,hu⟩
  have hm : 1≤m := by have := hb r; omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro v w he
    cases v with
    | inl v =>
      cases w with
      | inl w => exact congrArg Sum.inl (hi (by simpa [oneTailLabel] using he))
      | inr j => have := hb v; fin_cases j <;> simp [oneTailLabel] at he <;> omega
    | inr i =>
      cases w with
      | inl w => have := hb w; fin_cases i <;> simp [oneTailLabel] at he <;> omega
      | inr j => fin_cases i <;> fin_cases j <;> simp_all [oneTailLabel]
  · intro v
    cases v with
    | inl v => have := hb v; simp [oneTailLabel]; omega
    | inr i => fin_cases i <;> simp [oneTailLabel]
  · intro k hk
    by_cases hlo : k<2
    · have hh : k=0 ∨ k=1 := by omega
      rcases hh with rfl | rfl
      · exact ⟨.inr 1,by simp [oneTailLabel]⟩
      · exact ⟨.inr 3,by simp [oneTailLabel]⟩
    · by_cases hmid : k≤m+2
      · obtain ⟨v,hv⟩ := hs (k-2) (by omega)
        exact ⟨.inl v,by simp [oneTailLabel,hv]; omega⟩
      · have hh : k=m+3 ∨ k=m+4 := by omega
        rcases hh with rfl | rfl
        · exact ⟨.inr 2,by simp [oneTailLabel]⟩
        · exact ⟨.inr 0,by simp [oneTailLabel]⟩
  · intro e
    cases e with
    | inl e => rw [oneTail_old]; exact hp e
    | inr i => rw [oneTail_new _ _ _ _ hr]; fin_cases i <;> simp [oneTailWeight] <;> omega
  · intro d hd hdm
    by_cases hh : d≤m
    · obtain ⟨e,he,heuniq⟩ := hu d hd hh
      refine ⟨.inl e,?_,?_⟩
      · dsimp only; rw [oneTail_old]; exact he
      · intro z hz
        cases z with
        | inl z => rw [oneTail_old] at hz; exact congrArg Sum.inl (heuniq z hz)
        | inr i => rw [oneTail_new _ _ _ _ hr] at hz; fin_cases i <;> simp [oneTailWeight] at hz <;> omega
    · let i : Fin 4 := ⟨if d=m+1 then 0 else m+5-d,by split_ifs <;> omega⟩
      have hiw : oneTailWeight m i=d := by dsimp [i,oneTailWeight]; split_ifs <;> omega
      refine ⟨.inr i,?_,?_⟩
      · dsimp only; rw [oneTail_new _ _ _ _ hr]; exact hiw
      · intro z hz
        cases z with
        | inl e =>
          rw [oneTail_old] at hz
          have := hb (ends e).1
          have := hb (ends e).2
          simp only [Nat.dist] at hz
          omega
        | inr j =>
          rw [oneTail_new _ _ _ _ hr] at hz
          apply congrArg Sum.inr
          apply Fin.ext
          simp only [oneTailWeight] at hz hiw
          split_ifs at hz hiw <;> omega

theorem one_tail_alpha {V E : Type*} {m k : ℕ} {f : V → ℕ} {ends : E → V × V}
    (ha : Alpha k f ends) (hk : 1≤k) (hkm : k≤m) (r : V) (hr : f r=1) :
    Alpha (k+2) (oneTailLabel m f) (tailEnds ends r) := by
  intro e
  cases e with
  | inl e =>
    have := ha e
    simp only [tailEnds,oneTailLabel]
    omega
  | inr i => fin_cases i <;> simp [tailEnds,oneTailLabel,hr] <;> omega

end Math15Source10
#print axioms Math15Source10.one_tail_complete
#print axioms Math15Source10.one_tail_alpha
