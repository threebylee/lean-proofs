import MatchingLift

namespace Math15Source10
namespace Bistar

abbrev V (t p q : ℕ) := Fin (t+1) ⊕ Fin (p+q)
abbrev E (t p q : ℕ) := Fin t ⊕ Fin (p+q)

def ends (t p q : ℕ) : E t p q → V t p q × V t p q
  | .inl i => (.inl ⟨i.val,by omega⟩,.inl ⟨i.val+1,by omega⟩)
  | .inr j => (if j.val<p then .inl ⟨0,by omega⟩ else .inl ⟨t,by omega⟩,.inr j)

def label (t p q : ℕ) : V t p q → ℕ
  | .inl i => if i.val%2=0 then i.val/2 else t+q-i.val/2
  | .inr j => if j.val<p then t+p+q-j.val else t/2+j.val-p+1

def weight (t p q : ℕ) : E t p q → ℕ
  | .inl i => t+q-i.val
  | .inr j => if j.val<p then t+p+q-j.val else
      if t%2=0 then j.val-p+1 else p+q-j.val

theorem label_bound (t p q : ℕ) (v : V t p q) : label t p q v ≤ t+p+q := by
  cases v <;> simp only [label] <;> split_ifs <;> omega

theorem label_injective (t p q : ℕ) : Function.Injective (label t p q) := by
  intro v w he
  cases v with
  | inl i =>
    cases w with
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [label] at he
      split_ifs at he <;> omega
    | inr j =>
      simp only [label] at he
      split_ifs at he <;> omega
  | inr i =>
    cases w with
    | inl j =>
      simp only [label] at he
      split_ifs at he <;> omega
    | inr j =>
      apply congrArg Sum.inr
      apply Fin.ext
      simp only [label] at he
      split_ifs at he <;> omega

theorem label_onto (t p q k : ℕ) (hk : k ≤ t+p+q) : ∃ v, label t p q v = k := by
  let f : V t p q → Fin (t+p+q+1) := fun v => ⟨label t p q v,by have := label_bound t p q v; omega⟩
  have hi : Function.Injective f := by
    intro v w he
    apply label_injective t p q
    exact congrArg Fin.val he
  have hs : Function.Surjective f := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective f hi hn
    simp only [V,Fintype.card_sum,Fintype.card_fin] at hlt
    omega
  obtain ⟨v,hv⟩ := hs ⟨k,by omega⟩
  exact ⟨v,congrArg Fin.val hv⟩

theorem dist_weight (t p q : ℕ) (e : E t p q) :
    Nat.dist (label t p q (ends t p q e).1) (label t p q (ends t p q e).2) =
      weight t p q e := by
  cases e with
  | inl i =>
    simp only [ends,label,weight,Nat.dist]
    split_ifs <;> omega
  | inr j =>
    by_cases hj : j.val<p
    · simp [ends,label,weight,hj,Nat.dist]
    · simp only [ends,hj,↓reduceIte,label,weight,Nat.dist]
      split_ifs <;> omega

theorem weight_injective (t p q : ℕ) : Function.Injective (weight t p q) := by
  intro e g he
  cases e with
  | inl i =>
    cases g with
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [weight] at he
      omega
    | inr j =>
      simp only [weight] at he
      split_ifs at he <;> omega
  | inr i =>
    cases g with
    | inl j =>
      simp only [weight] at he
      split_ifs at he <;> omega
    | inr j =>
      apply congrArg Sum.inr
      apply Fin.ext
      simp only [weight] at he
      split_ifs at he <;> omega

theorem weight_pos (t p q : ℕ) (e : E t p q) : 0<weight t p q e := by
  cases e <;> simp only [weight] <;> (try split_ifs) <;> omega

theorem weight_onto (t p q d : ℕ) (hd : 1≤d) (hm : d≤t+p+q) :
    ∃ e, weight t p q e = d := by
  by_cases hsmall : d≤q
  · by_cases ht : t%2=0
    · refine ⟨.inr ⟨p+d-1,by omega⟩,?_⟩
      simp [weight,ht,show ¬ p+d-1<p by omega]
      omega
    · refine ⟨.inr ⟨p+q-d,by omega⟩,?_⟩
      simp [weight,ht,show ¬ p+q-d<p by omega]
      omega
  · by_cases hmid : d≤t+q
    · refine ⟨.inl ⟨t+q-d,by omega⟩,?_⟩
      simp only [weight]
      omega
    · refine ⟨.inr ⟨t+p+q-d,by omega⟩,?_⟩
      simp [weight,show t+p+q-d<p by omega]
      omega

theorem complete (t p q : ℕ) : Complete (t+p+q) (label t p q) (ends t p q) := by
  refine ⟨label_injective t p q,label_bound t p q,label_onto t p q,?_,?_⟩
  · intro e
    rw [dist_weight]
    exact weight_pos t p q e
  · intro d hd hm
    obtain ⟨e,he⟩ := weight_onto t p q d hd hm
    refine ⟨e,?_,?_⟩
    · dsimp only
      rw [dist_weight,he]
    · intro z hz
      apply weight_injective t p q
      rw [dist_weight] at hz
      exact hz.trans he.symm

end Bistar
end Math15Source10
#print axioms Math15Source10.Bistar.complete
