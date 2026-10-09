import PhysicalBistarEven
import Stem

set_option maxHeartbeats 800000
namespace Math15Source10

def tailTwelveEnds {V E : Type*} (ends : E → V × V) (r : V) :
    E ⊕ Fin 12 → (V ⊕ Fin 12) × (V ⊕ Fin 12)
  | .inl e => (.inl (ends e).1,.inl (ends e).2)
  | .inr i => (if h : i.val=0 then .inl r else .inr ⟨i.val-1,by omega⟩,.inr i)

def threeTailLabel {V : Type*} (m : ℕ) (f : V → ℕ) : V ⊕ Fin 12 → ℕ
  | .inl v => f v+6
  | .inr i => ![m+10,0,m+12,1,m+7,5,m+8,4,m+9,2,m+11,3] i

def threeTailWeight (m : ℕ) (i : Fin 12) := m + (![1,10,12,11,6,2,3,4,5,7,9,8] i)

theorem threeTail_old {V E : Type*} (m : ℕ) (f : V → ℕ) (ends : E → V × V) (r : V) (e : E) :
    Nat.dist (threeTailLabel m f (tailTwelveEnds ends r (.inl e)).1)
      (threeTailLabel m f (tailTwelveEnds ends r (.inl e)).2) =
      Nat.dist (f (ends e).1) (f (ends e).2) := by
  simp [tailTwelveEnds,threeTailLabel,Nat.dist]

theorem threeTail_new {V E : Type*} (m : ℕ) (f : V → ℕ) (ends : E → V × V) (r : V)
    (hr : f r=3) (i : Fin 12) :
    Nat.dist (threeTailLabel m f (tailTwelveEnds ends r (.inr i)).1)
      (threeTailLabel m f (tailTwelveEnds ends r (.inr i)).2) = threeTailWeight m i := by
  fin_cases i <;> simp [tailTwelveEnds,threeTailLabel,threeTailWeight,hr,Nat.dist] <;> omega

/-- Twelve-edge extension with a recurring endpoint label three. -/
theorem three_tail_complete {V E : Type*} [Fintype V] [Fintype E]
    {m : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (r : V) (hr : f r=3) :
    Complete (m+12) (threeTailLabel m f) (tailTwelveEnds ends r) := by
  have hm : 3≤m := by have := h.2.1 r; omega
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
      | inl w => exact congrArg Sum.inl (h.1 (by simpa [threeTailLabel] using he))
      | inr j => have := h.2.1 v; fin_cases j <;> simp [threeTailLabel] at he <;> omega
    | inr i =>
      cases w with
      | inl w => have := h.2.1 w; fin_cases i <;> simp [threeTailLabel] at he <;> omega
      | inr j => fin_cases i <;> fin_cases j <;> simp_all [threeTailLabel] <;> omega
  · intro v
    cases v with
    | inl v => have := h.2.1 v; simp [threeTailLabel]; omega
    | inr i => fin_cases i <;> simp [threeTailLabel] <;> omega
  · intro e
    cases e with
    | inl e => rw [threeTail_old]; exact h.2.2.2.1 e
    | inr i => rw [threeTail_new _ _ _ _ hr]; fin_cases i <;> simp [threeTailWeight] <;> omega
  · intro e g he
    dsimp only at he
    cases e with
    | inl e =>
      cases g with
      | inl g =>
        simp only [threeTail_old] at he
        exact congrArg Sum.inl (hiw he)
      | inr i =>
        rw [threeTail_old,threeTail_new _ _ _ _ hr] at he
        have := hd e
        fin_cases i <;> simp [threeTailWeight] at he <;> omega
    | inr i =>
      cases g with
      | inl e =>
        rw [threeTail_new _ _ _ _ hr,threeTail_old] at he
        have := hd e
        fin_cases i <;> simp [threeTailWeight] at he <;> omega
      | inr j =>
        rw [threeTail_new _ _ _ _ hr,threeTail_new _ _ _ _ hr] at he
        fin_cases i <;> fin_cases j <;> simp_all [threeTailWeight] <;> omega

theorem three_tail_alpha {V E : Type*} {m k : ℕ} {f : V → ℕ} {ends : E → V × V}
    (ha : Alpha k f ends) (hk : 3≤k) (hkm : k≤m) (r : V) (hr : f r=3) :
    Alpha (k+6) (threeTailLabel m f) (tailTwelveEnds ends r) := by
  intro e
  cases e with
  | inl e =>
    have := ha e
    simp only [tailTwelveEnds,threeTailLabel]
    omega
  | inr i => fin_cases i <;> simp [tailTwelveEnds,threeTailLabel,hr] <;> omega

/-- Twelve-edge extension at a low leaf three positions below the alpha boundary.
It fixes every old low label, raises every old high label by twelve, and puts
the new leaf three positions below the new boundary. -/
def nearThreeTailLabel {V : Type*} (m k : ℕ) (f : V → ℕ) :=
  reverseLabel (m+12) (k+6) (threeTailLabel m (reverseLabel m k f))

theorem near_three_tail_complete {V E : Type*} [Fintype V] [Fintype E] {m k : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (ha : Alpha k f ends) (hk : k≤m)
    (r : V) (hr : f r+3=k) :
    Complete (m+12) (nearThreeTailLabel m k f) (tailTwelveEnds ends r) := by
  have hr' : reverseLabel m k f r=3 := by simp only [reverseLabel]; split_ifs <;> omega
  exact reverse_complete
    (three_tail_complete (reverse_complete h ha hk) r hr')
    (three_tail_alpha (reverse_alpha h.2.1 ha) (by omega) hk r hr') (by omega)

theorem near_three_tail_alpha {V E : Type*} [Fintype V] [Fintype E] {m k : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (ha : Alpha k f ends) (hk : k≤m)
    (r : V) (hr : f r+3=k) :
    Alpha (k+6) (nearThreeTailLabel m k f) (tailTwelveEnds ends r) := by
  have hr' : reverseLabel m k f r=3 := by simp only [reverseLabel]; split_ifs <;> omega
  exact reverse_alpha
    (three_tail_complete (reverse_complete h ha hk) r hr').2.1
    (three_tail_alpha (reverse_alpha h.2.1 ha) (by omega) hk r hr')

theorem near_three_tail_old {V : Type*} {m k : ℕ} {f : V → ℕ}
    (hb : ∀v,f v≤m) (hk : k≤m) (v : V) :
    nearThreeTailLabel m k f (.inl v) = if f v≤k then f v else f v+12 := by
  have := hb v
  simp only [nearThreeTailLabel,reverseLabel,threeTailLabel]
  split_ifs <;> omega

theorem near_three_tail_last {V : Type*} (m k : ℕ) (f : V → ℕ) :
    nearThreeTailLabel m k f (.inr 11) = k+3 := by
  simp [nearThreeTailLabel,reverseLabel,threeTailLabel]


end Math15Source10
#print axioms Math15Source10.three_tail_complete
#print axioms Math15Source10.three_tail_alpha

#print axioms Math15Source10.near_three_tail_complete
#print axioms Math15Source10.near_three_tail_alpha
#print axioms Math15Source10.near_three_tail_old
