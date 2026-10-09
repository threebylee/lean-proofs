import PathAttachment

namespace Math15Source10

def walecki (n : ℕ) (v : Fin (n+1)) : ℕ :=
  if v.val%2=0 then v.val/2 else n-v.val/2

theorem walecki_dist (n : ℕ) (e : Fin n) :
    Nat.dist (walecki n (pathEnds n e).1) (walecki n (pathEnds n e).2)=n-e.val := by
  simp only [walecki,pathEnds,Nat.dist]
  split_ifs <;> omega

theorem walecki_complete (n : ℕ) : Complete n (walecki n) (pathEnds n) := by
  apply complete_finite _ _ _ (by simp) (by simp)
  · intro v w he
    apply Fin.ext
    simp only [walecki] at he
    split_ifs at he <;> omega
  · intro v; simp only [walecki]; split_ifs <;> omega
  · intro e; rw [walecki_dist]; omega
  · intro e g he
    dsimp only at he
    rw [walecki_dist,walecki_dist] at he
    apply Fin.ext; omega

theorem walecki_alpha (n : ℕ) : Alpha (n/2) (walecki n) (pathEnds n) := by
  intro e
  simp only [walecki,pathEnds]
  split_ifs <;> omega

theorem complement_alpha {V E : Type*} {m k : ℕ} {f : V → ℕ} {a : E → V × V}
    (hb : ∀v,f v≤m) (ha : Alpha k f a) (hk : k<m) :
    Alpha (m-k-1) (fun v => m-f v) a := by
  intro e
  have := hb (a e).1; have := hb (a e).2; have := ha e
  dsimp only; omega

theorem join_alpha {V W E F : Type*} {m k l : ℕ}
    {f : V → ℕ} {g : W → ℕ} {a : E → V × V} {b : F → W × W}
    (ha : Alpha k f a) (hb : Alpha l g b) (hl : l≤m) (u : V) (v : W)
    (hu : f u≤k) (hv : l<g v) :
    Alpha (k+l+1) (Math15.Labeling.joinLabel k (m+1) f g)
      (Math15.Labeling.joinEnds u v a b) := by
  intro e
  cases e with
  | inl e =>
    have := ha e
    simp only [Math15.Labeling.joinEnds,Math15.Labeling.joinLabel,Math15.Labeling.gap]
    split_ifs <;> omega
  | inr e =>
    cases e with
    | none =>
      simp only [Math15.Labeling.joinEnds,Math15.Labeling.joinLabel,Math15.Labeling.gap,if_pos hu]
      omega
    | some e =>
      have := hb e
      simp only [Math15.Labeling.joinEnds,Math15.Labeling.joinLabel]
      omega

/-- Read the first path backwards, cross the new bridge, then read the second
path forwards. This is the exact path represented by the joining operation. -/
def concatVertex (r m : ℕ) (i : Fin (r+m+1+1)) : Fin (r+1) ⊕ Fin (m+1) :=
  if h : i.val≤r then .inl ⟨r-i.val,by omega⟩ else .inr ⟨i.val-r-1,by omega⟩

def concatEdge (r m : ℕ) (i : Fin (r+m+1)) : Fin r ⊕ Option (Fin m) :=
  if h : i.val<r then .inl ⟨r-1-i.val,by omega⟩ else
    if h : i.val=r then .inr none else .inr (some ⟨i.val-r-1,by omega⟩)

theorem concatVertex_bijective (r m : ℕ) : Function.Bijective (concatVertex r m) := by
  apply bijective_of_injective_equal_card
  · intro i j he
    apply Fin.ext
    simp only [concatVertex] at he
    split_ifs at he <;> simp_all [Fin.ext_iff] <;> omega
  · simp; omega

theorem concatEdge_bijective (r m : ℕ) : Function.Bijective (concatEdge r m) := by
  apply bijective_of_injective_equal_card
  · intro i j he
    apply Fin.ext
    simp only [concatEdge] at he
    split_ifs at he <;> simp_all [Fin.ext_iff] <;> omega
  · simp; omega

theorem concat_endpoints (r m : ℕ) (e : Fin (r+m+1)) :
    let a := pathEnds (r+m+1) e
    let b := Math15.Labeling.joinEnds (0 : Fin (r+1)) (0 : Fin (m+1))
      (pathEnds r) (pathEnds m) (concatEdge r m e)
    (concatVertex r m a.1,concatVertex r m a.2)=b ∨
      (concatVertex r m a.2,concatVertex r m a.1)=b := by
  dsimp only
  by_cases hi : e.val<r
  · right
    simp [pathEnds,concatVertex,concatEdge,Math15.Labeling.joinEnds,hi,
      show e.val≤r by omega,show e.val+1≤r by omega,Prod.ext_iff,Fin.ext_iff]
    omega
  · by_cases he : e.val=r
    · left
      simp [pathEnds,concatVertex,concatEdge,Math15.Labeling.joinEnds,he,Prod.ext_iff,Fin.ext_iff]
    · left
      simp [pathEnds,concatVertex,concatEdge,Math15.Labeling.joinEnds,hi,he,
        show ¬e.val≤r by omega,show ¬e.val+1≤r by omega,Prod.ext_iff,Fin.ext_iff]
      omega

theorem concat_complete {r m : ℕ} {f : Fin (r+1) ⊕ Fin (m+1) → ℕ}
    (h : Complete (r+m+1) f (Math15.Labeling.joinEnds 0 0 (pathEnds r) (pathEnds m))) :
    Complete (r+m+1) (f ∘ concatVertex r m) (pathEnds (r+m+1)) := by
  apply complete_reindex h _ (concatVertex_bijective r m) _ (concatEdge_bijective r m)
  intro e
  rcases concat_endpoints r m e with he | he
  · have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
    dsimp only at h1 h2; rw [h1,h2]
  · have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
    dsimp only at h1 h2; rw [h1,h2,Nat.dist_comm]

theorem concat_alpha {r m k : ℕ} {f : Fin (r+1) ⊕ Fin (m+1) → ℕ}
    (h : Alpha k f (Math15.Labeling.joinEnds 0 0 (pathEnds r) (pathEnds m))) :
    Alpha k (f ∘ concatVertex r m) (pathEnds (r+m+1)) := by
  intro e
  have hh := h (concatEdge r m e)
  rcases concat_endpoints r m e with he | he
  · have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
    dsimp only at h1 h2
    dsimp only [Function.comp_apply]
    rw [h1,h2]; exact hh
  · have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
    dsimp only at h1 h2
    dsimp only [Function.comp_apply]
    rw [h1,h2]; exact hh.symm

end Math15Source10
#print axioms Math15Source10.walecki_complete
#print axioms Math15Source10.concat_complete
#print axioms Math15Source10.concat_alpha
#print axioms Math15Source10.join_alpha
