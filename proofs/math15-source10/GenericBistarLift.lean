import GenericCaterpillar
import EvenTwoArms

namespace Math15Source10.Bistar

def root (t p q : ℕ) : V t p q := .inl ⟨0,by omega⟩

def oddSide (t p q : ℕ) : E t p q → Bool
  | .inl i => decide (i.val%2=0)
  | .inr j => if j.val<p then false else decide (t%2=0)

def oddEnds (t p q : ℕ) := pairEnds (ends t p q) (oddSide t p q)
def oddLabel (t p q : ℕ) := pairLabel (t+p+q) (label t p q)

theorem odd_complete (t p q : ℕ) :
    Complete (2*(t+p+q)+1) (oddLabel t p q) (oddEnds t p q) :=
  matching_lift (complete t p q) (oddSide t p q)

theorem odd_zero (t p q : ℕ) : oddLabel t p q (root t p q,false) = 0 := by
  simp [oddLabel,pairLabel,root,label]

def evenSide (t p q : ℕ) : E t p q → Bool
  | .inl i => decide (i.val%2=1)
  | .inr j => if j.val<p then false else decide (t%2=1)

theorem evenSide_root (t p q : ℕ) (ht : 1≤t) (e : E t p q) :
    (ends t p q e).1 = root t p q ∨ (ends t p q e).2 = root t p q →
      evenSide t p q e = false := by
  intro he
  cases e with
  | inl i =>
    simp only [ends,root,Sum.inl.injEq,Fin.mk.injEq] at he
    have : i.val=0 := by omega
    simp [evenSide,this]
  | inr j =>
    by_cases hj : j.val<p
    · simp [evenSide,hj]
    · simp [ends,root,hj,Fin.ext_iff] at he
      omega

def evenEnds (t p q : ℕ) (ht : 1≤t) :=
  thinEnds (ends t p q) (evenSide t p q) (evenSide_root t p q ht)

def evenLabel (t p q : ℕ) (v : ThinV (root t p q)) :=
  2*(t+p+q) - thinLabel (t+p+q) (fun x => t+p+q-label t p q x) v

theorem even_complete (t p q : ℕ) (ht : 1≤t) :
    Complete (2*(t+p+q)) (evenLabel t p q) (evenEnds t p q ht) := by
  have hroot : t+p+q-label t p q (root t p q) = t+p+q := by simp [root,label]
  exact complete_reflect (singleton_lift (complete_reflect (complete t p q))
    (by omega) (root t p q) hroot (evenSide t p q) (evenSide_root t p q ht))

theorem even_zero (t p q : ℕ) :
    evenLabel t p q ⟨(root t p q,false),Or.inl rfl⟩ = 0 := by
  simp [evenLabel,thinLabel,root,label]

theorem odd_graceful (t p q : ℕ) :
    Math15.Graceful.IsGraceful (certificateGraph (odd_complete t p q)) :=
  certificateGraph_graceful (odd_complete t p q)

theorem even_graceful (t p q : ℕ) (ht : 1≤t) :
    Math15.Graceful.IsGraceful (certificateGraph (even_complete t p q ht)) := by
  classical
  exact certificateGraph_graceful (even_complete t p q ht)

end Math15Source10.Bistar
#print axioms Math15Source10.Bistar.odd_complete
#print axioms Math15Source10.Bistar.even_complete
#print axioms Math15Source10.Bistar.odd_zero
#print axioms Math15Source10.Bistar.even_zero
#print axioms Math15Source10.Bistar.even_graceful
