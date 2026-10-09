import RadialThree
import StemNearEnd
import StemPhysical

set_option linter.unusedSimpArgs false
namespace Math15Source10

theorem spider_equal_center_zero (n : ℕ) (hn : 1≤n) :
    ∃ f : Fin (n+n+1) ⊕ Fin (n-1+1) → ℕ,
      Complete (n+n+(n-1)+1) f (spiderEnds n n (n-1)) ∧ f (.inl (pathJunction n n))=0 := by
  classical
  obtain ⟨f,hf,h0⟩ := radial_three_all n hn
  let ev := Equiv.ofBijective (radialThreeVertex n hn) (radialThreeVertex_bijective n hn)
  let ee := Equiv.ofBijective (radialThreeEdge n hn) (radialThreeEdge_bijective n hn)
  have hc : Complete (3*n) (f ∘ ev.symm) (spiderEnds n n (n-1)) := by
    apply complete_reindex hf ev.symm ev.symm.bijective ee.symm ee.symm.bijective
    intro e
    rcases radialThree_endpoints n hn (ee.symm e) with h | h
    · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
      change ev (radialEnds 3 n (ee.symm e)).1=(spiderEnds n n (n-1) (ee (ee.symm e))).1 at h1
      change ev (radialEnds 3 n (ee.symm e)).2=(spiderEnds n n (n-1) (ee (ee.symm e))).2 at h2
      simp only [Equiv.apply_symm_apply] at h1 h2
      rw [(ev.symm_apply_eq).mpr h1.symm,(ev.symm_apply_eq).mpr h2.symm]
    · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
      change ev (radialEnds 3 n (ee.symm e)).1=(spiderEnds n n (n-1) (ee (ee.symm e))).2 at h1
      change ev (radialEnds 3 n (ee.symm e)).2=(spiderEnds n n (n-1) (ee (ee.symm e))).1 at h2
      simp only [Equiv.apply_symm_apply] at h1 h2
      rw [(ev.symm_apply_eq).mpr h2.symm,(ev.symm_apply_eq).mpr h1.symm,Nat.dist_comm]
  refine ⟨f ∘ ev.symm,?_,?_⟩
  · convert hc using 1 <;> omega
  · have hh : ev.symm (.inl (pathJunction n n))=none := (ev.symm_apply_eq).mpr rfl
    simpa only [Function.comp_apply,hh] using h0

def spider22Vertex (c : ℕ) : Fin (2+2+1) ⊕ Fin (c+1) → Fin (c+1+5)
  | .inl i => ⟨if i.val≤2 then 2-i.val else i.val,by split_ifs <;> omega⟩
  | .inr i => ⟨i.val+5,by omega⟩
def spider22Edge (c : ℕ) : Fin (2+2) ⊕ Option (Fin c) → Fin (c+1+4)
  | .inl e => ⟨if e.val<2 then 1-e.val else e.val,by split_ifs <;> omega⟩
  | .inr none => ⟨4,by omega⟩
  | .inr (some e) => ⟨e.val+5,by omega⟩
theorem spider22Vertex_bijective (c : ℕ) : Function.Bijective (spider22Vertex c) := by
  apply bijective_of_injective_equal_card
  · intro v w he
    have hh := congrArg Fin.val he
    rcases v with v | v <;> rcases w with w | w
    · simp only [spider22Vertex] at hh
      apply congrArg Sum.inl; apply Fin.ext; split_ifs at hh <;> omega
    · simp only [spider22Vertex] at hh; split_ifs at hh <;> omega
    · simp only [spider22Vertex] at hh; split_ifs at hh <;> omega
    · apply congrArg Sum.inr; apply Fin.ext; simp only [spider22Vertex] at hh; omega
  · simp; omega
theorem spider22Edge_bijective (c : ℕ) : Function.Bijective (spider22Edge c) := by
  apply bijective_of_injective_equal_card
  · intro v w he
    have hh := congrArg Fin.val he
    rcases v with v | v <;> rcases w with w | w
    · simp only [spider22Edge] at hh
      apply congrArg Sum.inl; apply Fin.ext; split_ifs at hh <;> omega
    · cases w <;> simp only [spider22Edge] at hh <;> split_ifs at hh <;> omega
    · cases v <;> simp only [spider22Edge] at hh <;> split_ifs at hh <;> omega
    · cases v <;> cases w <;> simp_all [spider22Edge,Fin.ext_iff]
  · simp; omega
theorem spider22_endpoints (c : ℕ) (e : Fin (2+2) ⊕ Option (Fin c)) :
    (spider22Vertex c (spiderEnds 2 2 c e).1,spider22Vertex c (spiderEnds 2 2 c e).2)=
      stemEnds (c+1) (spider22Edge c e) ∨
    (spider22Vertex c (spiderEnds 2 2 c e).1,spider22Vertex c (spiderEnds 2 2 c e).2)=
      ((stemEnds (c+1) (spider22Edge c e)).2,(stemEnds (c+1) (spider22Edge c e)).1) := by
  rcases e with e | e
  · fin_cases e <;> simp [spiderEnds,Math15.Labeling.joinEnds,pathEnds,pathJunction,
      spider22Vertex,spider22Edge,stemEnds,Fin.ext_iff,
      Nat.mod_eq_of_lt (show 2<c+1+5 by omega),
      Nat.mod_eq_of_lt (show 3<c+1+5 by omega),
      Nat.mod_eq_of_lt (show 4<c+1+5 by omega)]
  · cases e with
    | none => left; simp [spiderEnds,Math15.Labeling.joinEnds,pathJunction,spider22Vertex,spider22Edge,stemEnds,Fin.ext_iff]
    | some e =>
      left
      simp [spiderEnds,Math15.Labeling.joinEnds,pathEnds,spider22Vertex,spider22Edge,stemEnds,
        show e.val+5≠0 by omega,show e.val+5≠1 by omega,show e.val+5≠2 by omega,
        show e.val+5≠3 by omega,show e.val+5≠4 by omega,Prod.ext_iff,Fin.ext_iff]

theorem spider22_center_zero (c : ℕ) :
    ∃ f : Fin (2+2+1) ⊕ Fin (c+1) → ℕ,
      Complete (2+2+c+1) f (spiderEnds 2 2 c) ∧ f (.inl (pathJunction 2 2))=0 := by
  obtain ⟨f,hf,h0⟩ := Bistar.physical_root_zero (c+1) 2 0 (by omega)
  have hc := physical_to_stem (by convert hf using 1 <;> omega)
  have hh := complete_reindex hc _ (spider22Vertex_bijective c) _ (spider22Edge_bijective c)
    (spiderEnds 2 2 c) (by
      intro e
      rcases spider22_endpoints c e with h | h
      · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
        dsimp only at h1 h2; rw [h1,h2]
      · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
        dsimp only at h1 h2; rw [h1,h2,Nat.dist_comm])
  refine ⟨(f ∘ stemPhysicalVertex (c+1)) ∘ spider22Vertex c,?_,?_⟩
  · convert hh using 1 <;> omega
  · simpa [Function.comp_apply,spider22Vertex,pathJunction,stemPhysicalVertex] using h0

/-- Every ordered positive three-arm spider has a graceful labeling with
its center zero. The equal-even case follows by repeated uniform doubling. -/
theorem spider_center_zero_all (a b c : ℕ) (ha : 1≤a) (hb : a≤b) (hc : b≤c+1) :
    ∃ f : Fin (a+b+1) ⊕ Fin (c+1) → ℕ,
      Complete (a+b+c+1) f (spiderEnds a b c) ∧ f (.inl (pathJunction a b))=0 := by
  by_cases h22 : a=2 ∧ b=2
  · obtain ⟨rfl,rfl⟩ := h22; exact spider22_center_zero c
  · by_cases hk : a/2+b/2≤c
    · exact spider_center_zero_regular a b c ha (by omega) (by omega) hk
    · have hab : b=a := by omega
      have hca : c=a-1 := by omega
      subst b; subst c
      exact spider_equal_center_zero a ha

end Math15Source10
#print axioms Math15Source10.spider_center_zero_all
