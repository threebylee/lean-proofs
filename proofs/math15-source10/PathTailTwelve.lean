import AlphaTailThree
import PathBlocks

set_option linter.unusedSimpArgs false
namespace Math15Source10

def growPathVertex (n : ℕ) (v : Fin (n+12+1)) : Fin (n+1) ⊕ Fin 12 :=
  if h : v.val≤n then .inl ⟨v.val,by omega⟩ else .inr ⟨v.val-(n+1),by omega⟩
def growPathEdge (n : ℕ) (e : Fin (n+12)) : Fin n ⊕ Fin 12 :=
  if h : e.val<n then .inl ⟨e.val,h⟩ else .inr ⟨e.val-n,by omega⟩

theorem growPathVertex_bijective (n : ℕ) : Function.Bijective (growPathVertex n) := by
  apply bijective_of_injective_equal_card
  · intro v w he
    apply Fin.ext
    simp only [growPathVertex] at he
    split_ifs at he <;> simp_all [Fin.ext_iff] <;> omega
  · simp

theorem growPathEdge_bijective (n : ℕ) : Function.Bijective (growPathEdge n) := by
  apply bijective_of_injective_equal_card
  · intro v w he
    apply Fin.ext
    simp only [growPathEdge] at he
    split_ifs at he <;> simp_all [Fin.ext_iff] <;> omega
  · simp

theorem growPath_endpoints (n : ℕ) (e : Fin (n+12)) :
    (growPathVertex n (pathEnds (n+12) e).1,growPathVertex n (pathEnds (n+12) e).2)=
    tailTwelveEnds (pathEnds n) ⟨n,by omega⟩ (growPathEdge n e) := by
  by_cases he : e.val<n
  · simp [pathEnds,growPathVertex,growPathEdge,tailTwelveEnds,he,
      show e.val≤n by omega,show e.val+1≤n by omega,Prod.ext_iff,Fin.ext_iff]
  · by_cases hn : e.val=n
    · simp [pathEnds,growPathVertex,growPathEdge,tailTwelveEnds,he,hn,Prod.ext_iff,Fin.ext_iff]
    · simp [pathEnds,growPathVertex,growPathEdge,tailTwelveEnds,he,
        show ¬e.val≤n by omega,show ¬e.val+1≤n by omega,show e.val-n≠0 by omega,
        Prod.ext_iff,Fin.ext_iff]
      omega

theorem growPath_complete {n : ℕ} {f : Fin (n+1) ⊕ Fin 12 → ℕ}
    (h : Complete (n+12) f (tailTwelveEnds (pathEnds n) ⟨n,by omega⟩)) :
    Complete (n+12) (f ∘ growPathVertex n) (pathEnds (n+12)) := by
  apply complete_reindex h _ (growPathVertex_bijective n) _ (growPathEdge_bijective n)
  intro e
  have he := growPath_endpoints n e
  have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
  dsimp only at h1 h2
  rw [h1,h2]

theorem growPath_alpha {n k : ℕ} {f : Fin (n+1) ⊕ Fin 12 → ℕ}
    (h : Alpha k f (tailTwelveEnds (pathEnds n) ⟨n,by omega⟩)) :
    Alpha k (f ∘ growPathVertex n) (pathEnds (n+12)) := by
  intro e
  have he := growPath_endpoints n e
  have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
  dsimp only at h1 h2
  dsimp only [Function.comp_apply]
  rw [h1,h2]
  exact h (growPathEdge n e)

end Math15Source10
#print axioms Math15Source10.growPath_complete
#print axioms Math15Source10.growPath_alpha
