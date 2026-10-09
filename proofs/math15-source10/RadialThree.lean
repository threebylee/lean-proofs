import UniformSpider

set_option linter.unusedSimpArgs false
namespace Math15Source10

def radialThreeVertex (n : ℕ) (hn : 1≤n) : RadialV 3 n → Fin (n+n+1) ⊕ Fin (n-1+1)
  | none => .inl (pathJunction n n)
  | some (j,i) => if j.val=0 then .inl ⟨n-1-i.val,by omega⟩
    else if j.val=1 then .inl ⟨n+1+i.val,by omega⟩ else .inr ⟨i.val,by omega⟩
def radialThreeEdge (n : ℕ) (hn : 1≤n) (e : RadialE 3 n) : Fin (n+n) ⊕ Option (Fin (n-1)) :=
  if e.1.val=0 then .inl ⟨n-1-e.2.val,by omega⟩
  else if e.1.val=1 then .inl ⟨n+e.2.val,by omega⟩
  else if h : e.2.val=0 then .inr none else .inr (some ⟨e.2.val-1,by omega⟩)

theorem radialThreeVertex_bijective (n : ℕ) (hn : 1≤n) : Function.Bijective (radialThreeVertex n hn) := by
  apply bijective_of_injective_equal_card
  · intro v w he
    cases v with
    | none =>
      cases w with
      | none => rfl
      | some w =>
        obtain ⟨j,i⟩ := w
        fin_cases j <;> simp [radialThreeVertex,pathJunction,Fin.ext_iff] at he <;> omega
    | some v =>
      obtain ⟨j,i⟩ := v
      cases w with
      | none => fin_cases j <;> simp [radialThreeVertex,pathJunction,Fin.ext_iff] at he <;> omega
      | some w =>
        obtain ⟨k,l⟩ := w
        fin_cases j <;> fin_cases k <;> simp_all [radialThreeVertex,Fin.ext_iff] <;> omega
  · simp [RadialV]; omega

theorem radialThreeEdge_bijective (n : ℕ) (hn : 1≤n) : Function.Bijective (radialThreeEdge n hn) := by
  apply bijective_of_injective_equal_card
  · rintro ⟨j,i⟩ ⟨k,l⟩ he
    fin_cases j <;> fin_cases k <;> simp only [radialThreeEdge] at he
    all_goals split_ifs at he <;> simp_all [Prod.ext_iff,Fin.ext_iff] <;> omega
  · simp [RadialE]; omega

theorem radialThree_endpoints (n : ℕ) (hn : 1≤n) (e : RadialE 3 n) :
    (radialThreeVertex n hn (radialEnds 3 n e).1,radialThreeVertex n hn (radialEnds 3 n e).2)=
      spiderEnds n n (n-1) (radialThreeEdge n hn e) ∨
    (radialThreeVertex n hn (radialEnds 3 n e).1,radialThreeVertex n hn (radialEnds 3 n e).2)=
      ((spiderEnds n n (n-1) (radialThreeEdge n hn e)).2,
       (spiderEnds n n (n-1) (radialThreeEdge n hn e)).1) := by
  obtain ⟨j,i⟩ := e
  fin_cases j
  · right
    by_cases hi : i.val=0 <;>
      simp [radialEnds,radialThreeVertex,radialThreeEdge,spiderEnds,Math15.Labeling.joinEnds,
        pathEnds,pathJunction,hi,Prod.ext_iff,Fin.ext_iff] <;> omega
  · left
    by_cases hi : i.val=0 <;>
      simp [radialEnds,radialThreeVertex,radialThreeEdge,spiderEnds,Math15.Labeling.joinEnds,
        pathEnds,pathJunction,hi,Prod.ext_iff,Fin.ext_iff] <;> omega
  · left
    by_cases hi : i.val=0 <;>
      simp [radialEnds,radialThreeVertex,radialThreeEdge,spiderEnds,Math15.Labeling.joinEnds,
        pathEnds,pathJunction,hi,Prod.ext_iff,Fin.ext_iff] <;> omega

theorem radial_three_odd (n : ℕ) (hn : 1≤n) (ho : n%2=1) : RadialZero 3 n := by
  obtain ⟨f,hf,h0⟩ := spider_center_zero_regular n n (n-1) hn hn (by omega) (by omega)
  have hc := complete_reindex hf _ (radialThreeVertex_bijective n hn) _ (radialThreeEdge_bijective n hn)
    (radialEnds 3 n) (by
      intro e
      rcases radialThree_endpoints n hn e with h | h
      · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
        dsimp only at h1 h2; rw [h1,h2]
      · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
        dsimp only at h1 h2; rw [h1,h2,Nat.dist_comm])
  refine ⟨f ∘ radialThreeVertex n hn,?_,?_⟩
  · convert hc using 1 <;> omega
  · exact h0

theorem radial_three_all (n : ℕ) (hn : 1≤n) : RadialZero 3 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases ho : n%2=1
    · exact radial_three_odd n hn ho
    · have hh := radial_zero_double (by omega : 1≤3) (show 1≤n/2 by omega)
        (ih (n/2) (by omega) (by omega))
      simpa only [show 2*(n/2)=n by omega] using hh

end Math15Source10
#print axioms Math15Source10.radial_three_all
