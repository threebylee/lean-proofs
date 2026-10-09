import SixModel
import CaseSelection

namespace Math15Source10

theorem complete_transport {V W E F : Type*} {m : ℕ} {f : V → ℕ}
    {ends : E → V × V} (h : Complete m f ends) (ev : V ≃ W) (ee : E ≃ F)
    (ends' : F → W × W)
    (hp : ∀i,(ev (ends i).1,ev (ends i).2)=ends' (ee i) ∨
      (ev (ends i).1,ev (ends i).2)=(ends' (ee i)).swap) :
    Complete m (f ∘ ev.symm) ends' := by
  apply complete_reindex h ev.symm ev.symm.bijective ee.symm ee.symm.bijective
  intro i
  rcases hp (ee.symm i) with hh | hh
  · have h1 := congrArg Prod.fst hh; have h2 := congrArg Prod.snd hh
    simp only [Equiv.apply_symm_apply,Prod.fst,Prod.snd] at h1 h2
    rw [←h1,←h2,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  · have h1 := congrArg Prod.fst hh; have h2 := congrArg Prod.snd hh
    simp only [Equiv.apply_symm_apply,Prod.fst_swap,Prod.snd_swap,Prod.fst,Prod.snd] at h1 h2
    rw [←h1,←h2,Equiv.symm_apply_apply,Equiv.symm_apply_apply,Nat.dist_comm]

theorem six_complete_of_regular {a b c d e f : ℕ} (hd : 1≤d)
    (h : ∃F,Complete (e+f+(d+(a+b+c+1))) F (regularEnds a b c d e f)) :
    ∃F,Complete (a+b+(c+1)+d+e+f) F (sixEnds a b (c+1) d e f) := by
  obtain ⟨F,hF⟩ := h
  have hh := complete_transport hF
    (Equiv.ofBijective _ (regularSixVertex_bijective a b c d e f))
    (Equiv.ofBijective _ (regularSixEdge_bijective a b c d e f))
    (sixEnds a b (c+1) d e f) (regularSix_endpoints a b c d e f hd)
  refine ⟨F ∘ (Equiv.ofBijective _ (regularSixVertex_bijective a b c d e f)).symm,?_⟩
  convert hh using 1 <;> omega

def armsTwoMap : ArmsV 2 2 2 2 2 → Fin 5 × Bool
  | .inl i => (0,decide (i.val=1))
  | .inr (.inl i) => (1,decide (i.val=1))
  | .inr (.inr (.inl i)) => (2,decide (i.val=1))
  | .inr (.inr (.inr (.inl i))) => (3,decide (i.val=1))
  | .inr (.inr (.inr (.inr i))) => (4,decide (i.val=1))

noncomputable def armsTwoEquiv : ArmsV 2 2 2 2 2 ≃ Fin 5 × Bool := Equiv.ofBijective armsTwoMap (by decide)

theorem six_all_two (d : ℕ) (hd : 1≤d) :
    ∃F,Complete (2+2+2+d+2+2) F (sixEnds 2 2 2 d 2 2) := by
  obtain ⟨F,hF,_⟩ := Bistar.physical_root_zero d 3 2 hd
  let ev : SixV 2 2 2 d 2 2 ≃ Bistar.PhysicalV d 3 2 :=
    Equiv.sumCongr (Equiv.refl _) armsTwoEquiv
  let ee : SixE 2 2 2 d 2 2 ≃ Bistar.PhysicalE d 3 2 :=
    Equiv.sumCongr (Equiv.refl _) armsTwoEquiv
  have hh : Complete (d+2*(3+2)) (F ∘ ev) (sixEnds 2 2 2 d 2 2) := by
    apply complete_reindex hF ev ev.bijective ee ee.bijective
    intro i
    have he : (ev (sixEnds 2 2 2 d 2 2 i).1,ev (sixEnds 2 2 2 d 2 2 i).2)=
        Bistar.physicalEnds d 3 2 (ee i) := by
      rcases i with i | i
      · rfl
      · rcases i with i | i
        · fin_cases i <;> simp [ev,ee,armsTwoEquiv,armsTwoMap,sixEnds,armEnds,Bistar.physicalEnds]
        · rcases i with i | i
          · fin_cases i <;> simp [ev,ee,armsTwoEquiv,armsTwoMap,sixEnds,armEnds,Bistar.physicalEnds]
          · rcases i with i | i
            · fin_cases i <;> simp [ev,ee,armsTwoEquiv,armsTwoMap,sixEnds,armEnds,Bistar.physicalEnds]
            · rcases i with i | i <;> fin_cases i <;>
                simp [ev,ee,armsTwoEquiv,armsTwoMap,sixEnds,armEnds,Bistar.physicalEnds]
    have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
    dsimp only at h1 h2
    rw [h1,h2]
  refine ⟨F ∘ ev,?_⟩
  convert hh using 1 <;> omega

theorem six_labeling_cases (a b c d e f : ℕ) (ha : 1≤a) (hb : 1≤b) (hc : 1≤c)
    (hd : 1≤d) (he : 1≤e) (hf : 1≤f)
    (hcase : (e≠2 ∨ f≠2) ∧ a≤b ∧ b≤c ∨
      e=2 ∧ f=2 ∧ ExceptionalArmCase a b c) :
    ∃F,Complete (a+b+c+d+e+f) F (sixEnds a b c d e f) := by
  rcases hcase with ⟨hex,hab,hbc⟩ | ⟨rfl,rfl,hex⟩
  · obtain ⟨c',rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : c≠0)
    exact six_complete_of_regular hd (regular_complete a b c' d e f ha hab (by omega) he hf hex)
  · cases hex with
    | allTwo ha hb hc => subst a; subst b; subst c; exact six_all_two d hd
    | large ha hab hbc =>
      obtain ⟨c',rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : c≠0)
      obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
      exact six_complete_of_regular (by omega) (model_to_regular22 (model_large_all ha hab (by omega)))
    | shortOne ha hb hc hex =>
      subst c
      obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
      exact six_complete_of_regular (by omega) (model_to_regular22 (model_short_one ha hb hex))
    | shortTwo ha hb hc hex =>
      subst c
      obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
      exact six_complete_of_regular (by omega) (model_to_regular22 (model_short_two ha hb hex))

end Math15Source10
#print axioms Math15Source10.six_labeling_cases
