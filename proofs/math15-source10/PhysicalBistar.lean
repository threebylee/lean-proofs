import GenericBistarLift

namespace Math15Source10

theorem complete_reindex {V W E F : Type*} {m : ℕ} {f : W → ℕ}
    {ends : F → W × W} (h : Complete m f ends)
    (φ : V → W) (hφ : Function.Bijective φ) (ψ : E → F) (hψ : Function.Bijective ψ)
    (ends' : E → V × V)
    (hd : ∀ e, Nat.dist (f (φ (ends' e).1)) (f (φ (ends' e).2)) =
      Nat.dist (f (ends (ψ e)).1) (f (ends (ψ e)).2)) :
    Complete m (f ∘ φ) ends' := by
  refine ⟨h.1.comp hφ.1,fun v => h.2.1 (φ v),?_,?_,?_⟩
  · intro k hk
    obtain ⟨w,hw⟩ := h.2.2.1 k hk
    obtain ⟨v,rfl⟩ := hφ.2 w
    exact ⟨v,hw⟩
  · intro e
    simpa only [Function.comp_apply,hd] using h.2.2.2.1 (ψ e)
  · intro d h1 h2
    obtain ⟨z,hz,hu⟩ := h.2.2.2.2 d h1 h2
    obtain ⟨e,rfl⟩ := hψ.2 z
    refine ⟨e,?_,?_⟩
    · dsimp only [Function.comp_apply]
      rw [hd]
      exact hz
    · intro g hg
      apply hψ.1
      apply hu
      simpa only [Function.comp_apply,hd] using hg

theorem bijective_of_injective_equal_card {V W : Type*} [Fintype V] [Fintype W]
    (f : V → W) (hi : Function.Injective f) (hc : Fintype.card V = Fintype.card W) :
    Function.Bijective f := by
  refine ⟨hi,?_⟩
  by_contra hn
  have := Fintype.card_lt_of_injective_not_surjective f hi hn
  omega

namespace Bistar

/-- Direct path-and-arms presentation: bridge vertices 0,...,D, and a
midpoint and leaf on each of p+q terminal arms. -/
abbrev PhysicalV (D p q : ℕ) := Fin (D+1) ⊕ (Fin (p+q) × Bool)
abbrev PhysicalE (D p q : ℕ) := Fin D ⊕ (Fin (p+q) × Bool)

def physicalEnds (D p q : ℕ) : PhysicalE D p q → PhysicalV D p q × PhysicalV D p q
  | .inl i => (.inl ⟨i.val,by omega⟩,.inl ⟨i.val+1,by omega⟩)
  | .inr (j,false) => (if j.val<p then .inl ⟨0,by omega⟩ else .inl ⟨D,by omega⟩,
      .inr (j,false))
  | .inr (j,true) => (.inr (j,false),.inr (j,true))

def oddVertex (t p q : ℕ) : PhysicalV (2*t+1) p q → V t p q × Bool
  | .inl i => (.inl ⟨i.val/2,by omega⟩,decide ((i.val/2+i.val)%2=1))
  | .inr (j,b) => (.inr j,if j.val<p then b else b.xor (decide (t%2=0)))

def oddEdge (t p q : ℕ) : PhysicalE (2*t+1) p q → V t p q ⊕ E t p q
  | .inl i => if h : i.val%2=0 then .inl (.inl ⟨i.val/2,by omega⟩)
      else .inr (.inl ⟨i.val/2,by omega⟩)
  | .inr (j,false) => .inr (.inr j)
  | .inr (j,true) => .inl (.inr j)

theorem oddVertex_injective (t p q : ℕ) : Function.Injective (oddVertex t p q) := by
  intro v w he
  cases v with
  | inl i =>
    cases w with
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [oddVertex,Prod.mk.injEq,Sum.inl.injEq,Fin.mk.injEq] at he
      rcases he with ⟨he,hb⟩
      by_cases hi : (i.val/2+i.val)%2=1 <;>
        by_cases hj : (j.val/2+j.val)%2=1 <;> simp_all <;> omega
    | inr j => simp [oddVertex] at he
  | inr i =>
    cases w with
    | inl j => simp [oddVertex] at he
    | inr j =>
      obtain ⟨i,b⟩ := i
      obtain ⟨j,c⟩ := j
      simp only [oddVertex,Prod.mk.injEq,Sum.inr.injEq] at he
      rcases he with ⟨rfl,he⟩
      apply congrArg Sum.inr
      by_cases hi : i.val<p <;> by_cases ht : t%2=0 <;> cases b <;> cases c <;>
        simp [hi,ht] at he ⊢

theorem oddVertex_bijective (t p q : ℕ) : Function.Bijective (oddVertex t p q) := by
  apply bijective_of_injective_equal_card _ (oddVertex_injective t p q)
  simp [PhysicalV,V,Fintype.card_sum,Fintype.card_prod]
  omega

theorem oddEdge_injective (t p q : ℕ) : Function.Injective (oddEdge t p q) := by
  intro e g he
  cases e with
  | inl i =>
    cases g with
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [oddEdge] at he
      split_ifs at he <;> simp_all [Fin.ext_iff] <;> omega
    | inr j =>
      obtain ⟨j,b⟩ := j
      cases b <;> simp only [oddEdge] at he <;> split_ifs at he <;> simp_all
  | inr i =>
    obtain ⟨i,b⟩ := i
    cases g with
    | inl j =>
      cases b <;> simp only [oddEdge] at he <;> split_ifs at he <;> simp_all
    | inr j =>
      obtain ⟨j,c⟩ := j
      cases b <;> cases c <;> simp_all [oddEdge]

theorem oddEdge_bijective (t p q : ℕ) : Function.Bijective (oddEdge t p q) := by
  apply bijective_of_injective_equal_card _ (oddEdge_injective t p q)
  simp [PhysicalE,V,E,Fintype.card_sum,Fintype.card_prod]
  omega

theorem odd_endpoints (t p q : ℕ) (e : PhysicalE (2*t+1) p q) :
    (oddVertex t p q (physicalEnds (2*t+1) p q e).1,
      oddVertex t p q (physicalEnds (2*t+1) p q e).2) = oddEnds t p q (oddEdge t p q e) ∨
    (oddVertex t p q (physicalEnds (2*t+1) p q e).2,
      oddVertex t p q (physicalEnds (2*t+1) p q e).1) = oddEnds t p q (oddEdge t p q e) := by
  cases e with
  | inl i =>
    by_cases hi : i.val%2=0
    · by_cases hp : i.val/2%2=0
      · left
        simp [physicalEnds,oddVertex,oddEdge,oddEnds,pairEnds,hi,Prod.ext_iff,Fin.ext_iff]
        omega
      · right
        simp [physicalEnds,oddVertex,oddEdge,oddEnds,pairEnds,hi,Prod.ext_iff,Fin.ext_iff]
        omega
    · left
      simp [physicalEnds,oddVertex,oddEdge,oddEnds,pairEnds,oddSide,ends,hi,
        Prod.ext_iff,Fin.ext_iff]
      omega
  | inr jb =>
    obtain ⟨j,b⟩ := jb
    cases b with
    | false =>
      left
      by_cases hj : j.val<p <;> by_cases ht : t%2=0 <;>
        simp [physicalEnds,oddVertex,oddEdge,oddEnds,pairEnds,oddSide,ends,hj,ht,
          Prod.ext_iff,Fin.ext_iff] <;> omega
    | true =>
      by_cases hj : j.val<p
      · left; simp [physicalEnds,oddVertex,oddEdge,oddEnds,pairEnds,hj]
      · by_cases ht : t%2=0
        · right; simp [physicalEnds,oddVertex,oddEdge,oddEnds,pairEnds,hj,ht]
        · left; simp [physicalEnds,oddVertex,oddEdge,oddEnds,pairEnds,hj,ht]

def oddPhysicalLabel (t p q : ℕ) := oddLabel t p q ∘ oddVertex t p q

theorem odd_physical_complete (t p q : ℕ) :
    Complete (2*(t+p+q)+1) (oddPhysicalLabel t p q) (physicalEnds (2*t+1) p q) := by
  apply complete_reindex (odd_complete t p q) (oddVertex t p q) (oddVertex_bijective t p q)
    (oddEdge t p q) (oddEdge_bijective t p q)
  intro e
  rcases odd_endpoints t p q e with he | he
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
#print axioms Math15Source10.Bistar.odd_physical_complete
