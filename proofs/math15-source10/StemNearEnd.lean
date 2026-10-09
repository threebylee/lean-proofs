import PhysicalBistarEven
import PathZeroBalanced

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
namespace Math15Source10

def nearEndVertex (D : ℕ) (v : Fin (D+2+5)) : Bistar.PhysicalV D 1 2 :=
  if h0 : v.val=0 then .inl ⟨D,by omega⟩ else
  if h1 : v.val=1 then .inr (1,false) else
  if h2 : v.val=2 then .inr (1,true) else
  if h3 : v.val=3 then .inr (2,false) else
  if h4 : v.val=4 then .inr (2,true) else
  if h : v.val≤D+4 then .inl ⟨D+4-v.val,by omega⟩ else
  if v.val=D+5 then .inr (0,false) else .inr (0,true)

def nearEndEdge (D : ℕ) (e : Fin (D+2+4)) : Bistar.PhysicalE D 1 2 :=
  if h0 : e.val=0 then .inr (1,false) else
  if h1 : e.val=1 then .inr (1,true) else
  if h2 : e.val=2 then .inr (2,false) else
  if h3 : e.val=3 then .inr (2,true) else
  if h : e.val<D+4 then .inl ⟨D+3-e.val,by omega⟩ else
  if e.val=D+4 then .inr (0,false) else .inr (0,true)

theorem nearEndVertex_bijective (D : ℕ) (hD : 1≤D) : Function.Bijective (nearEndVertex D) := by
  apply bijective_of_injective_equal_card
  · intro v w he
    apply Fin.ext
    have hh := congrArg (fun z : Bistar.PhysicalV D 1 2 => match z with
      | .inl i => i.val | .inr (j,b) => D+1+2*j.val+(if b then 1 else 0)) he
    simp only [nearEndVertex] at hh
    split_ifs at hh <;> norm_num at hh <;> omega
  · simp [Bistar.PhysicalV]

theorem nearEndEdge_bijective (D : ℕ) (hD : 1≤D) : Function.Bijective (nearEndEdge D) := by
  apply bijective_of_injective_equal_card
  · intro v w he
    apply Fin.ext
    have hh := congrArg (fun z : Bistar.PhysicalE D 1 2 => match z with
      | .inl i => i.val | .inr (j,b) => D+2*j.val+(if b then 1 else 0)) he
    simp only [nearEndEdge] at hh
    split_ifs at hh <;> norm_num at hh <;> omega
  · simp [Bistar.PhysicalE]

theorem nearEnd_endpoints (D : ℕ) (hD : 1≤D) (e : Fin (D+2+4)) :
    (nearEndVertex D (stemEnds (D+2) e).1,nearEndVertex D (stemEnds (D+2) e).2)=
      Bistar.physicalEnds D 1 2 (nearEndEdge D e) ∨
    (nearEndVertex D (stemEnds (D+2) e).2,nearEndVertex D (stemEnds (D+2) e).1)=
      Bistar.physicalEnds D 1 2 (nearEndEdge D e) := by
  by_cases h0 : e.val=0
  · left; simp [stemEnds,nearEndVertex,nearEndEdge,Bistar.physicalEnds,h0]
  by_cases h1 : e.val=1
  · left; simp [stemEnds,nearEndVertex,nearEndEdge,Bistar.physicalEnds,h1,
      Nat.mod_eq_of_lt (show 2<D+2+5 by omega)]
  by_cases h2 : e.val=2
  · left; simp [stemEnds,nearEndVertex,nearEndEdge,Bistar.physicalEnds,h2,
      Nat.mod_eq_of_lt (show 3<D+2+5 by omega)]
  by_cases h3 : e.val=3
  · left; simp [stemEnds,nearEndVertex,nearEndEdge,Bistar.physicalEnds,h3,
      Nat.mod_eq_of_lt (show 3<D+2+5 by omega),Nat.mod_eq_of_lt (show 4<D+2+5 by omega)]
  by_cases h4 : e.val=4
  · right
    simp [stemEnds,nearEndVertex,nearEndEdge,Bistar.physicalEnds,h4,
      show 4<D+4 by omega,show 5≤D+4 by omega,Prod.ext_iff,Fin.ext_iff]
    omega
  by_cases hm : e.val<D+4
  · right
    simp [stemEnds,nearEndVertex,nearEndEdge,Bistar.physicalEnds,h0,h1,h2,h3,h4,hm,
      show e.val≤D+4 by omega,show e.val+1≤D+4 by omega,
      show e.val+1≠0 by omega,show e.val+1≠1 by omega,show e.val+1≠2 by omega,
      show e.val+1≠3 by omega,show e.val+1≠4 by omega,Prod.ext_iff,Fin.ext_iff]
    omega
  · have he : e.val=D+4 ∨ e.val=D+5 := by omega
    rcases he with he | he
    · left
      simp [stemEnds,nearEndVertex,nearEndEdge,Bistar.physicalEnds,he,
        show D≠0 by omega,show D+4≠4 by omega,show D+4≠0 by omega,show D+4≠1 by omega,
        show D+4≠2 by omega,show D+4≠3 by omega,Prod.ext_iff,Fin.ext_iff]
    · left
      simp [stemEnds,nearEndVertex,nearEndEdge,Bistar.physicalEnds,he,
        show D+5≠4 by omega,show D+5≠0 by omega,show D+5≠1 by omega,
        show D+5≠2 by omega,show D+5≠3 by omega,Prod.ext_iff,Fin.ext_iff]

theorem Bistar.physical_root_zero (D p q : ℕ) (hD : 1≤D) :
    ∃ f : Bistar.PhysicalV D p q → ℕ,
      Complete (D+2*(p+q)) f (Bistar.physicalEnds D p q) ∧ f (.inl 0)=0 := by
  by_cases he : D%2=0
  · generalize ht : D/2=t at *
    have hd : D=2*t := by omega
    subst D
    refine ⟨Bistar.evenPhysicalLabel t p q,?_,?_⟩
    · convert Bistar.even_physical_complete t p q (by omega) using 1 <;> omega
    · simp [Bistar.evenPhysicalLabel,Bistar.evenVertex,Bistar.evenLabel,thinLabel,Bistar.label]
  · generalize ht : D/2=t at *
    have hd : D=2*t+1 := by omega
    subst D
    refine ⟨Bistar.oddPhysicalLabel t p q,?_,?_⟩
    · convert Bistar.odd_physical_complete t p q using 1 <;> omega
    · simp [Bistar.oddPhysicalLabel,Bistar.oddVertex,Bistar.oddLabel,pairLabel,Bistar.label]

theorem stem_two_before_end_zero (D : ℕ) (hD : 1≤D) : MarkZero (D+2) (D+4) := by
  obtain ⟨f,hf,hr⟩ := Bistar.physical_root_zero D 1 2 hD
  refine ⟨f ∘ nearEndVertex D,?_,?_⟩
  · apply complete_reindex (show Complete (D+2+4) f (Bistar.physicalEnds D 1 2) by simpa using hf)
      _ (nearEndVertex_bijective D hD) _ (nearEndEdge_bijective D hD)
    intro e
    rcases nearEnd_endpoints D hD e with he | he
    · have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
      dsimp only at h1 h2; rw [h1,h2]
    · have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
      dsimp only at h1 h2; rw [h1,h2,Nat.dist_comm]
  · intro v hv
    have he : nearEndVertex D v=.inl 0 := by
      simp [nearEndVertex,hv,show D+4≠0 by omega,show D+4≠1 by omega,
        show D+4≠2 by omega,show D+4≠3 by omega,show D≠0 by omega,show D+4≠4 by omega]
    simpa only [Function.comp_apply,he] using hr

theorem model_short_two {a b s : ℕ} (ha : 1≤a) (hb : 1≤b) (hex : a≠2 ∨ b≠2) :
    ModelGraceful a b 1 s := by
  apply model_of_markzero (pathZero_all a b ha hb hex)
  convert stem_two_before_end_zero (s+1) (by omega) using 1 <;> omega

end Math15Source10
#print axioms Math15Source10.stem_two_before_end_zero
#print axioms Math15Source10.model_short_two
