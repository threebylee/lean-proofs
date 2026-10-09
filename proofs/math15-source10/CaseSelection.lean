import RegularExceptional

namespace Math15Source10

noncomputable def perm012 : Equiv.Perm (Fin 3) := Equiv.ofBijective ![0,1,2] (by decide)
noncomputable def perm021 : Equiv.Perm (Fin 3) := Equiv.ofBijective ![0,2,1] (by decide)
noncomputable def perm102 : Equiv.Perm (Fin 3) := Equiv.ofBijective ![1,0,2] (by decide)
noncomputable def perm120 : Equiv.Perm (Fin 3) := Equiv.ofBijective ![1,2,0] (by decide)
noncomputable def perm201 : Equiv.Perm (Fin 3) := Equiv.ofBijective ![2,0,1] (by decide)
noncomputable def perm210 : Equiv.Perm (Fin 3) := Equiv.ofBijective ![2,1,0] (by decide)

theorem order_three_arms (L : Fin 3 → ℕ) :
    ∃ σ : Equiv.Perm (Fin 3),L (σ 0)≤L (σ 1) ∧ L (σ 1)≤L (σ 2) := by
  by_cases h01 : L 0≤L 1
  · by_cases h12 : L 1≤L 2
    · exact ⟨perm012,by simpa [perm012] using And.intro h01 h12⟩
    · by_cases h02 : L 0≤L 2
      · exact ⟨perm021,by simp [perm021]; omega⟩
      · exact ⟨perm201,by simp [perm201]; omega⟩
  · by_cases h02 : L 0≤L 2
    · exact ⟨perm102,by simp [perm102]; omega⟩
    · by_cases h12 : L 1≤L 2
      · exact ⟨perm120,by simp [perm120]; omega⟩
      · exact ⟨perm210,by simp [perm210]; omega⟩

inductive ExceptionalArmCase (a b c : ℕ) : Prop
  | large (ha : 3≤a) (hab : a≤b) (hbc : b≤c)
  | shortOne (ha : 1≤a) (hb : 1≤b) (hc : c=1) (hex : a≠2 ∨ b≠2)
  | shortTwo (ha : 1≤a) (hb : 1≤b) (hc : c=2) (hex : a≠2 ∨ b≠2)
  | allTwo (ha : a=2) (hb : b=2) (hc : c=2)

/-- Every positive triple enters one of the checked exceptional constructions.
This includes the easily missed (1,2,2) triple: choose a length-two third arm. -/
theorem exceptional_arm_case_selection (L : Fin 3 → ℕ) (hL : ∀i,1≤L i) :
    ∃ σ : Equiv.Perm (Fin 3),ExceptionalArmCase (L (σ 0)) (L (σ 1)) (L (σ 2)) := by
  obtain ⟨σ,h01,h12⟩ := order_three_arms L
  have h0 := hL (σ 0)
  have h1 := hL (σ 1)
  have h2 := hL (σ 2)
  by_cases hlarge : 3≤L (σ 0)
  · exact ⟨σ,.large hlarge h01 h12⟩
  · by_cases hfirst : L (σ 0)=1
    · by_cases h22 : L (σ 1)=2 ∧ L (σ 2)=2
      · exact ⟨σ,.shortTwo h0 h1 h22.2 (Or.inl (by omega))⟩
      · refine ⟨perm120.trans σ,?_⟩
        simp only [Equiv.trans_apply,perm120,Equiv.ofBijective_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
        exact .shortOne h1 h2 hfirst (by omega)
    · have hfirst2 : L (σ 0)=2 := by omega
      by_cases h22 : L (σ 1)=2 ∧ L (σ 2)=2
      · exact ⟨σ,.allTwo hfirst2 h22.1 h22.2⟩
      · refine ⟨perm120.trans σ,?_⟩
        simp only [Equiv.trans_apply,perm120,Equiv.ofBijective_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
        exact .shortTwo h1 h2 hfirst2 (by omega)

end Math15Source10
#print axioms Math15Source10.exceptional_arm_case_selection
