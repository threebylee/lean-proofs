import PhysicalBistar

namespace Math15Source10

theorem Complete.card_vertex {V E : Type*} [Fintype V] {m : ℕ} {f : V → ℕ}
    {ends : E → V × V} (h : Complete m f ends) : Fintype.card V=m+1 := by
  let ff : V → Fin (m+1) := fun v => ⟨f v,by have := h.2.1 v; omega⟩
  have hh : Function.Bijective ff := by
    constructor
    · intro v w he; exact h.1 (congrArg Fin.val he)
    · intro k; obtain ⟨v,hv⟩ := h.2.2.1 k.val (by omega)
      exact ⟨v,Fin.ext hv⟩
  simpa using Fintype.card_congr (Equiv.ofBijective ff hh)

theorem Complete.card_edge {V E : Type*} [Fintype E] {m : ℕ} {f : V → ℕ}
    {ends : E → V × V} (h : Complete m f ends) : Fintype.card E=m := by
  let ww (e : E) := Nat.dist (f (ends e).1) (f (ends e).2)
  have hb (e : E) : ww e≤m := by
    have := h.2.1 (ends e).1; have := h.2.1 (ends e).2
    dsimp [ww]; simp only [Nat.dist]; omega
  have hp (e : E) : 0<ww e := h.2.2.2.1 e
  let ee : E → Fin m := fun e => ⟨ww e-1,by have := hp e; have := hb e; omega⟩
  have hh : Function.Bijective ee := by
    constructor
    · intro e g he
      have heq := congrArg Fin.val he
      have hep := hp e; have hgp := hp g
      obtain ⟨z,hz,hu⟩ := h.2.2.2.2 (ww e) (by omega) (hb e)
      have hg : ww g=ww e := by dsimp [ee] at heq; omega
      exact (hu e rfl).trans (hu g hg).symm
    · intro k
      obtain ⟨e,he,_⟩ := h.2.2.2.2 (k.val+1) (by omega) (by omega)
      refine ⟨e,Fin.ext ?_⟩
      dsimp [ee,ww]; rw [he]; omega
  simpa using Fintype.card_congr (Equiv.ofBijective ee hh)

namespace Bistar

def evenVertex (t p q : ℕ) : PhysicalV (2*t) p q → ThinV (root t p q)
  | .inl i => ⟨(.inl ⟨(i.val+1)/2,by omega⟩,decide (((i.val+1)/2+i.val)%2=1)),by
      by_cases hi : i.val=0
      · left; simp [hi]
      · right; simp [root,Fin.ext_iff]; omega⟩
  | .inr (j,b) => ⟨(.inr j,if j.val<p then b else b.xor (decide (t%2=1))),Or.inr (by simp [root])⟩

def evenEdge (t p q : ℕ) : PhysicalE (2*t) p q → {v : V t p q // v≠root t p q} ⊕ E t p q
  | .inl i => if h : i.val%2=0 then .inr (.inl ⟨i.val/2,by omega⟩)
      else .inl ⟨.inl ⟨i.val/2+1,by omega⟩,by simp [root,Fin.ext_iff]⟩
  | .inr (j,false) => .inr (.inr j)
  | .inr (j,true) => .inl ⟨.inr j,by simp [root]⟩

theorem evenVertex_injective (t p q : ℕ) : Function.Injective (evenVertex t p q) := by
  intro v w he
  have he := congrArg Subtype.val he
  cases v with
  | inl i =>
    cases w with
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [evenVertex,Prod.mk.injEq,Sum.inl.injEq,Fin.mk.injEq] at he
      rcases he with ⟨he,hb⟩
      by_cases hi : ((i.val+1)/2+i.val)%2=1 <;>
        by_cases hj : ((j.val+1)/2+j.val)%2=1 <;> simp_all <;> omega
    | inr j => simp [evenVertex] at he
  | inr i =>
    cases w with
    | inl j => simp [evenVertex] at he
    | inr j =>
      obtain ⟨i,b⟩ := i
      obtain ⟨j,c⟩ := j
      simp only [evenVertex,Prod.mk.injEq,Sum.inr.injEq] at he
      rcases he with ⟨rfl,he⟩
      apply congrArg Sum.inr
      by_cases hi : i.val<p <;> by_cases ht : t%2=1 <;> cases b <;> cases c <;>
        simp [hi,ht] at he ⊢

theorem evenVertex_bijective (t p q : ℕ) (ht : 1≤t) : Function.Bijective (evenVertex t p q) := by
  apply bijective_of_injective_equal_card _ (evenVertex_injective t p q)
  rw [(even_complete t p q ht).card_vertex]
  simp [PhysicalV]; omega

theorem evenEdge_injective (t p q : ℕ) : Function.Injective (evenEdge t p q) := by
  intro e g he
  cases e with
  | inl i =>
    cases g with
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [evenEdge] at he
      split_ifs at he <;> simp_all [Subtype.ext_iff,Fin.ext_iff] <;> omega
    | inr j =>
      obtain ⟨j,b⟩ := j
      cases b <;> simp only [evenEdge] at he <;> split_ifs at he <;> simp_all [Subtype.ext_iff]
  | inr i =>
    obtain ⟨i,b⟩ := i
    cases g with
    | inl j =>
      cases b <;> simp only [evenEdge] at he <;> split_ifs at he <;> simp_all [Subtype.ext_iff]
    | inr j =>
      obtain ⟨j,c⟩ := j
      cases b <;> cases c <;> simp_all [evenEdge,Subtype.ext_iff]

theorem evenEdge_bijective (t p q : ℕ) (ht : 1≤t) : Function.Bijective (evenEdge t p q) := by
  apply bijective_of_injective_equal_card _ (evenEdge_injective t p q)
  rw [(even_complete t p q ht).card_edge]
  simp [PhysicalE]; omega

theorem even_endpoints (t p q : ℕ) (ht : 1≤t) (e : PhysicalE (2*t) p q) :
    (evenVertex t p q (physicalEnds (2*t) p q e).1,
      evenVertex t p q (physicalEnds (2*t) p q e).2) = evenEnds t p q ht (evenEdge t p q e) ∨
    (evenVertex t p q (physicalEnds (2*t) p q e).2,
      evenVertex t p q (physicalEnds (2*t) p q e).1) = evenEnds t p q ht (evenEdge t p q e) := by
  cases e with
  | inl i =>
    by_cases hi : i.val%2=0
    · left
      simp [physicalEnds,evenVertex,evenEdge,evenEnds,thinEnds,thinPort,evenSide,ends,hi,
        Prod.ext_iff,Subtype.ext_iff,Fin.ext_iff]
      omega
    · by_cases hp : (i.val/2+1)%2=1
      · left
        simp [physicalEnds,evenVertex,evenEdge,evenEnds,thinEnds,hi,
          Prod.ext_iff,Subtype.ext_iff,Fin.ext_iff]
        omega
      · right
        simp [physicalEnds,evenVertex,evenEdge,evenEnds,thinEnds,hi,
          Prod.ext_iff,Subtype.ext_iff,Fin.ext_iff]
        omega
  | inr jb =>
    obtain ⟨j,b⟩ := jb
    cases b with
    | false =>
      left
      by_cases hj : j.val<p <;> by_cases ht' : t%2=1 <;>
        simp [physicalEnds,evenVertex,evenEdge,evenEnds,thinEnds,thinPort,evenSide,ends,hj,ht',
          Prod.ext_iff,Subtype.ext_iff,Fin.ext_iff] <;> omega
    | true =>
      by_cases hj : j.val<p
      · left; simp [physicalEnds,evenVertex,evenEdge,evenEnds,thinEnds,hj,Subtype.ext_iff]
      · by_cases ht' : t%2=1
        · right; simp [physicalEnds,evenVertex,evenEdge,evenEnds,thinEnds,hj,ht',Subtype.ext_iff]
        · left; simp [physicalEnds,evenVertex,evenEdge,evenEnds,thinEnds,hj,ht',Subtype.ext_iff]

def evenPhysicalLabel (t p q : ℕ) := evenLabel t p q ∘ evenVertex t p q

theorem even_physical_complete (t p q : ℕ) (ht : 1≤t) :
    Complete (2*(t+p+q)) (evenPhysicalLabel t p q) (physicalEnds (2*t) p q) := by
  apply complete_reindex (even_complete t p q ht) (evenVertex t p q) (evenVertex_bijective t p q ht)
    (evenEdge t p q) (evenEdge_bijective t p q ht)
  intro e
  rcases even_endpoints t p q ht e with he | he
  · have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only [Prod.fst,Prod.snd] at h1 h2
    rw [h1,h2]
  · have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only [Prod.fst,Prod.snd] at h1 h2
    rw [h1,h2,Nat.dist_comm]

end Bistar
end Math15Source10
#print axioms Math15Source10.Bistar.even_physical_complete
