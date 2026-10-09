import PhysicalBistar
import AlphaReverse
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Math15Source10

theorem complete_finite {V E : Type*} [Fintype V] [Fintype E]
    (m : ℕ) (f : V → ℕ) (ends : E → V × V)
    (hv : Fintype.card V=m+1) (he : Fintype.card E=m)
    (hi : Function.Injective f) (hb : ∀v,f v≤m)
    (hp : ∀e,0<Nat.dist (f (ends e).1) (f (ends e).2))
    (hw : Function.Injective (fun e => Nat.dist (f (ends e).1) (f (ends e).2))) :
    Complete m f ends := by
  let fv : V → Fin (m+1) := fun v => ⟨f v,by have := hb v; omega⟩
  have hfv : Function.Bijective fv := by
    apply bijective_of_injective_equal_card
    · intro v w hh; exact hi (congrArg Fin.val hh)
    · simpa using hv
  let fe : E → Fin m := fun e => ⟨Nat.dist (f (ends e).1) (f (ends e).2)-1,by
    have := hp e
    have := hb (ends e).1
    have := hb (ends e).2
    simp only [Nat.dist] at *
    omega⟩
  have hfeval : ∀e,(fe e).val+1=Nat.dist (f (ends e).1) (f (ends e).2) := by
    intro e; have := hp e; dsimp [fe]; omega
  have hfe : Function.Bijective fe := by
    apply bijective_of_injective_equal_card
    · intro e g hh
      apply hw
      have := congrArg Fin.val hh
      have := hfeval e
      have := hfeval g
      dsimp only
      omega
    · simpa using he
  refine ⟨hi,hb,?_,hp,?_⟩
  · intro k hk
    obtain ⟨v,hv⟩ := hfv.2 ⟨k,by omega⟩
    exact ⟨v,congrArg Fin.val hv⟩
  · intro d hd hdm
    obtain ⟨e,he⟩ := hfe.2 ⟨d-1,by omega⟩
    have hed : Nat.dist (f (ends e).1) (f (ends e).2)=d := by
      have := congrArg Fin.val he
      have := hfeval e
      dsimp only at *
      omega
    exact ⟨e,hed,fun g hg => hw (hg.trans hed.symm)⟩

/-- S(2,2,s), with s=0 interpreted as the four-edge path rooted at its center. -/
def stemEnds (s : ℕ) (e : Fin (s+4)) : Fin (s+5) × Fin (s+5) :=
  if e.val=0 then (0,1) else if e.val=1 then (1,2) else if e.val=2 then (0,3)
  else if e.val=3 then (3,4) else
    (if e.val=4 then 0 else ⟨e.val,by omega⟩,⟨e.val+1,by omega⟩)

def stemLeaf (s : ℕ) : Fin (s+5) := ⟨if s=0 then 0 else s+4,by split_ifs <;> omega⟩

def growFin (n : ℕ) (i : Fin (n+4)) : Fin n ⊕ Fin 4 :=
  if h : i.val<n then .inl ⟨i.val,h⟩ else .inr ⟨i.val-n,by omega⟩

theorem growFin_injective (n : ℕ) : Function.Injective (growFin n) := by
  intro i j he
  apply Fin.ext
  simp only [growFin] at he
  split_ifs at he <;> simp_all [Fin.ext_iff] <;> omega

theorem growFin_bijective (n : ℕ) : Function.Bijective (growFin n) := by
  apply bijective_of_injective_equal_card _ (growFin_injective n)
  simp

/-- Exact endpoint correspondence for extending the stem by four edges. -/
theorem grow_stem_ends (s : ℕ) (e : Fin (s+4+4)) :
    (growFin (s+5) (stemEnds (s+4) e).1,growFin (s+5) (stemEnds (s+4) e).2) =
      tailEnds (stemEnds s) (stemLeaf s) (growFin (s+4) e) := by
  by_cases h0 : e.val=0
  · simp [stemEnds,growFin,tailEnds,h0]
  by_cases h1 : e.val=1
  · simp [stemEnds,growFin,tailEnds,h1,Nat.mod_eq_of_lt (show 2<s+5+4 by omega),show 2<s+5 by omega,Fin.ext_iff,Nat.mod_eq_of_lt (show 2<s+5 by omega)]
  by_cases h2 : e.val=2
  · simp [stemEnds,growFin,tailEnds,h2,Nat.mod_eq_of_lt (show 3<s+5+4 by omega),show 3<s+5 by omega,Fin.ext_iff,Nat.mod_eq_of_lt (show 3<s+5 by omega)]
  by_cases h3 : e.val=3
  · simp [stemEnds,growFin,tailEnds,h3,Nat.mod_eq_of_lt (show 3<s+5+4 by omega),Nat.mod_eq_of_lt (show 4<s+5+4 by omega),show 3<s+5 by omega,show 4<s+5 by omega,Fin.ext_iff,Nat.mod_eq_of_lt (show 3<s+5 by omega),Nat.mod_eq_of_lt (show 4<s+5 by omega)]
  by_cases ho : e.val<s+4
  · have hv : e.val<s+5 := by omega
    have hw : e.val+1<s+5 := by omega
    by_cases h4 : e.val=4
    · simp [stemEnds,growFin,tailEnds,h4,show 0<s by omega]
    · simp [stemEnds,growFin,tailEnds,h0,h1,h2,h3,h4,ho,hv,hw]
  · have he : e.val=s+4 ∨ e.val=s+5 ∨ e.val=s+6 ∨ e.val=s+7 := by omega
    rcases he with he | he | he | he
    · by_cases hs : s=0
      · subst s; simp [stemEnds,growFin,tailEnds,stemLeaf,he]
      · simp [stemEnds,growFin,tailEnds,stemLeaf,he,hs,Fin.ext_iff]
    · simp [stemEnds,growFin,tailEnds,he,Fin.ext_iff]
    · simp [stemEnds,growFin,tailEnds,he,Fin.ext_iff]
    · simp [stemEnds,growFin,tailEnds,he,Fin.ext_iff]

/-- Reindex the attached tail onto the direct Fin-indexed stem graph. -/
theorem grow_stem_complete (s : ℕ) (f : Fin (s+5) ⊕ Fin 4 → ℕ)
    (h : Complete (s+4+4) f (tailEnds (stemEnds s) (stemLeaf s))) :
    Complete (s+4+4) (f ∘ growFin (s+5)) (stemEnds (s+4)) := by
  apply complete_reindex h _ (growFin_bijective _) _ (growFin_bijective _)
  intro e
  have hh := grow_stem_ends s e
  have h1 := congrArg Prod.fst hh
  have h2 := congrArg Prod.snd hh
  dsimp only at h1 h2
  rw [h1,h2]

theorem grow_stem_alpha (s k : ℕ) (f : Fin (s+5) ⊕ Fin 4 → ℕ)
    (h : Alpha k f (tailEnds (stemEnds s) (stemLeaf s))) :
    Alpha k (f ∘ growFin (s+5)) (stemEnds (s+4)) := by
  intro e
  have hh := h (growFin (s+4) e)
  have he := grow_stem_ends s e
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp only [Function.comp_apply] at h1 h2 ⊢
  rw [h1,h2]
  exact hh

theorem grow_stem_leaf (s : ℕ) : growFin (s+5) (stemLeaf (s+4)) = .inr 3 := by
  simp [growFin,stemLeaf,show s+4≠0 by omega,show ¬s+4+4<s+5 by omega,Fin.ext_iff]

end Math15Source10
#print axioms Math15Source10.complete_finite
#print axioms Math15Source10.grow_stem_complete
