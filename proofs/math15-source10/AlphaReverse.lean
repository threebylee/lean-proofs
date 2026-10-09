import AlphaTail

namespace Math15Source10

def reverseLabel {V : Type*} (m k : ℕ) (f : V → ℕ) (v : V) :=
  if f v≤k then k-f v else m+k+1-f v

theorem reverse_dist {V E : Type*} {m k : ℕ} {f : V → ℕ} {ends : E → V × V}
    (hb : ∀v,f v≤m) (ha : Alpha k f ends) (e : E) :
    Nat.dist (reverseLabel m k f (ends e).1) (reverseLabel m k f (ends e).2) =
      m+1-Nat.dist (f (ends e).1) (f (ends e).2) := by
  have := hb (ends e).1
  have := hb (ends e).2
  have := ha e
  simp only [reverseLabel,Nat.dist]
  split_ifs <;> omega

theorem reverse_complete {V E : Type*} {m k : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (ha : Alpha k f ends) (hk : k≤m) :
    Complete m (reverseLabel m k f) ends := by
  rcases h with ⟨hi,hb,hs,hp,hu⟩
  have hdmax : ∀e,Nat.dist (f (ends e).1) (f (ends e).2)≤m := by
    intro e
    have := hb (ends e).1
    have := hb (ends e).2
    simp only [Nat.dist]
    omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro v w he
    have := hb v
    have := hb w
    apply hi
    simp only [reverseLabel] at he
    split_ifs at he <;> omega
  · intro v
    have := hb v
    simp only [reverseLabel]
    split_ifs <;> omega
  · intro d hd
    by_cases hdk : d≤k
    · obtain ⟨v,hv⟩ := hs (k-d) (by omega)
      refine ⟨v,?_⟩
      simp only [reverseLabel,hv]
      split_ifs <;> omega
    · obtain ⟨v,hv⟩ := hs (m+k+1-d) (by omega)
      refine ⟨v,?_⟩
      simp only [reverseLabel,hv]
      split_ifs <;> omega
  · intro e
    rw [reverse_dist hb ha]
    have := hdmax e
    omega
  · intro d hd hdm
    obtain ⟨e,he,heuniq⟩ := hu (m+1-d) (by omega) (by omega)
    refine ⟨e,?_,?_⟩
    · dsimp only
      rw [reverse_dist hb ha,he]
      omega
    · intro z hz
      rw [reverse_dist hb ha] at hz
      have := hdmax z
      exact heuniq z (by dsimp only; omega)

theorem reverse_alpha {V E : Type*} {m k : ℕ} {f : V → ℕ} {ends : E → V × V}
    (hb : ∀v,f v≤m) (ha : Alpha k f ends) : Alpha k (reverseLabel m k f) ends := by
  intro e
  have := hb (ends e).1
  have := hb (ends e).2
  have := ha e
  simp only [reverseLabel]
  split_ifs <;> omega

/-- Four-edge extension at a low leaf one position below the alpha boundary.
It fixes every old low label, raises every old high label by four, and puts
the new leaf one position below the new boundary. -/
def nearTailLabel {V : Type*} (m k : ℕ) (f : V → ℕ) :=
  reverseLabel (m+4) (k+2) (oneTailLabel m (reverseLabel m k f))

theorem near_tail_complete {V E : Type*} {m k : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (ha : Alpha k f ends) (hk : k≤m)
    (r : V) (hr : f r+1=k) :
    Complete (m+4) (nearTailLabel m k f) (tailEnds ends r) := by
  have hr' : reverseLabel m k f r=1 := by simp only [reverseLabel]; split_ifs <;> omega
  exact reverse_complete
    (one_tail_complete (reverse_complete h ha hk) r hr')
    (one_tail_alpha (reverse_alpha h.2.1 ha) (by omega) hk r hr') (by omega)

theorem near_tail_alpha {V E : Type*} {m k : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (ha : Alpha k f ends) (hk : k≤m)
    (r : V) (hr : f r+1=k) :
    Alpha (k+2) (nearTailLabel m k f) (tailEnds ends r) := by
  have hr' : reverseLabel m k f r=1 := by simp only [reverseLabel]; split_ifs <;> omega
  exact reverse_alpha
    (one_tail_complete (reverse_complete h ha hk) r hr').2.1
    (one_tail_alpha (reverse_alpha h.2.1 ha) (by omega) hk r hr')

theorem near_tail_old {V : Type*} {m k : ℕ} {f : V → ℕ}
    (hb : ∀v,f v≤m) (hk : k≤m) (v : V) :
    nearTailLabel m k f (.inl v) = if f v≤k then f v else f v+4 := by
  have := hb v
  simp only [nearTailLabel,reverseLabel,oneTailLabel]
  split_ifs <;> omega

theorem near_tail_last {V : Type*} (m k : ℕ) (f : V → ℕ) :
    nearTailLabel m k f (.inr 3) = k+1 := by
  simp [nearTailLabel,reverseLabel,oneTailLabel]

end Math15Source10
#print axioms Math15Source10.reverse_complete
#print axioms Math15Source10.near_tail_complete
#print axioms Math15Source10.near_tail_alpha
#print axioms Math15Source10.near_tail_old
