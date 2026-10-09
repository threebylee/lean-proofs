import PhysicalBistarEven
import Stem

namespace Math15Source10

def tailEightEnds {V E : Type*} (ends : E → V × V) (r : V) :
    E ⊕ Fin 8 → (V ⊕ Fin 8) × (V ⊕ Fin 8)
  | .inl e => (.inl (ends e).1,.inl (ends e).2)
  | .inr i => (if h : i.val=0 then .inl r else .inr ⟨i.val-1,by omega⟩,.inr i)

def twoTailLabel {V : Type*} (m : ℕ) (f : V → ℕ) : V ⊕ Fin 8 → ℕ
  | .inl v => f v+4
  | .inr i => ![m+7,1,m+8,0,m+5,3,m+6,2] i

def twoTailWeight (m : ℕ) (i : Fin 8) := m + (![1,6,7,8,5,2,3,4] i)

theorem twoTail_old {V E : Type*} (m : ℕ) (f : V → ℕ) (ends : E → V × V) (r : V) (e : E) :
    Nat.dist (twoTailLabel m f (tailEightEnds ends r (.inl e)).1)
      (twoTailLabel m f (tailEightEnds ends r (.inl e)).2) =
      Nat.dist (f (ends e).1) (f (ends e).2) := by
  simp [tailEightEnds,twoTailLabel,Nat.dist]

theorem twoTail_new {V E : Type*} (m : ℕ) (f : V → ℕ) (ends : E → V × V) (r : V)
    (hr : f r=2) (i : Fin 8) :
    Nat.dist (twoTailLabel m f (tailEightEnds ends r (.inr i)).1)
      (twoTailLabel m f (tailEightEnds ends r (.inr i)).2) = twoTailWeight m i := by
  fin_cases i <;> simp [tailEightEnds,twoTailLabel,twoTailWeight,hr,Nat.dist] <;> omega

/-- Eight-edge extension with a recurring endpoint label two. -/
theorem two_tail_complete {V E : Type*} [Fintype V] [Fintype E]
    {m : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (r : V) (hr : f r=2) :
    Complete (m+8) (twoTailLabel m f) (tailEightEnds ends r) := by
  have hm : 2≤m := by have := h.2.1 r; omega
  have hd (e : E) : Nat.dist (f (ends e).1) (f (ends e).2)≤m := by
    have := h.2.1 (ends e).1; have := h.2.1 (ends e).2
    simp only [Nat.dist]; omega
  have hiw : Function.Injective (fun e => Nat.dist (f (ends e).1) (f (ends e).2)) := by
    intro e g he
    obtain ⟨z,hz,hu⟩ := h.2.2.2.2 _ (h.2.2.2.1 e) (hd e)
    exact (hu e rfl).trans (hu g he.symm).symm
  apply complete_finite _ _ _
  · simp [h.card_vertex]
  · simp [h.card_edge]
  · intro v w he
    cases v with
    | inl v =>
      cases w with
      | inl w => exact congrArg Sum.inl (h.1 (by simpa [twoTailLabel] using he))
      | inr j => have := h.2.1 v; fin_cases j <;> simp [twoTailLabel] at he <;> omega
    | inr i =>
      cases w with
      | inl w => have := h.2.1 w; fin_cases i <;> simp [twoTailLabel] at he <;> omega
      | inr j => fin_cases i <;> fin_cases j <;> simp_all [twoTailLabel] <;> omega
  · intro v
    cases v with
    | inl v => have := h.2.1 v; simp [twoTailLabel]; omega
    | inr i => fin_cases i <;> simp [twoTailLabel] <;> omega
  · intro e
    cases e with
    | inl e => rw [twoTail_old]; exact h.2.2.2.1 e
    | inr i => rw [twoTail_new _ _ _ _ hr]; fin_cases i <;> simp [twoTailWeight] <;> omega
  · intro e g he
    dsimp only at he
    cases e with
    | inl e =>
      cases g with
      | inl g =>
        simp only [twoTail_old] at he
        exact congrArg Sum.inl (hiw he)
      | inr i =>
        rw [twoTail_old,twoTail_new _ _ _ _ hr] at he
        have := hd e
        fin_cases i <;> simp [twoTailWeight] at he <;> omega
    | inr i =>
      cases g with
      | inl e =>
        rw [twoTail_new _ _ _ _ hr,twoTail_old] at he
        have := hd e
        fin_cases i <;> simp [twoTailWeight] at he <;> omega
      | inr j =>
        rw [twoTail_new _ _ _ _ hr,twoTail_new _ _ _ _ hr] at he
        fin_cases i <;> fin_cases j <;> simp_all [twoTailWeight] <;> omega

theorem two_tail_alpha {V E : Type*} {m k : ℕ} {f : V → ℕ} {ends : E → V × V}
    (ha : Alpha k f ends) (hk : 2≤k) (hkm : k≤m) (r : V) (hr : f r=2) :
    Alpha (k+4) (twoTailLabel m f) (tailEightEnds ends r) := by
  intro e
  cases e with
  | inl e =>
    have := ha e
    simp only [tailEightEnds,twoTailLabel]
    omega
  | inr i => fin_cases i <;> simp [tailEightEnds,twoTailLabel,hr] <;> omega

end Math15Source10
#print axioms Math15Source10.two_tail_complete
#print axioms Math15Source10.two_tail_alpha
