import PhysicalBistarEven
import Stem

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Math15Source10

def stemPhysicalVertex (s : ℕ) (i : Fin (s+5)) : Bistar.PhysicalV s 2 0 :=
  if h0 : i.val=0 then .inl 0 else if h : i.val<5 then
    .inr (⟨(i.val-1)/2,by omega⟩,decide (i.val%2=0)) else
    .inl ⟨i.val-4,by omega⟩

def stemPhysicalEdge (s : ℕ) (i : Fin (s+4)) : Bistar.PhysicalE s 2 0 :=
  if h : i.val<4 then .inr (⟨i.val/2,by omega⟩,decide (i.val%2=1)) else
    .inl ⟨i.val-4,by omega⟩

def stemPhysicalBack {s : ℕ} : Bistar.PhysicalV s 2 0 → ℕ
  | .inl i => if i.val=0 then 0 else i.val+4
  | .inr (j,b) => 2*j.val+1+(if b then 1 else 0)

theorem stemPhysical_left (s : ℕ) (i : Fin (s+5)) :
    stemPhysicalBack (stemPhysicalVertex s i)=i.val := by
  by_cases h0 : i.val=0
  · simp [stemPhysicalVertex,stemPhysicalBack,h0]
  by_cases h5 : i.val<5
  · have hh : i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 := by omega
    rcases hh with hh | hh | hh | hh <;> simp [stemPhysicalVertex,stemPhysicalBack,hh]
  · simp [stemPhysicalVertex,stemPhysicalBack,h0,h5,show i.val-4≠0 by omega]
    omega

theorem stemPhysicalVertex_bijective (s : ℕ) : Function.Bijective (stemPhysicalVertex s) := by
  apply bijective_of_injective_equal_card
  · intro i j he
    apply Fin.ext
    have hh := congrArg stemPhysicalBack he
    simpa only [stemPhysical_left] using hh
  · simp

theorem stemPhysicalEdge_bijective (s : ℕ) : Function.Bijective (stemPhysicalEdge s) := by
  apply bijective_of_injective_equal_card
  · intro i j he
    apply Fin.ext
    simp only [stemPhysicalEdge] at he
    split_ifs at he <;> simp_all [Prod.mk.injEq,Fin.ext_iff] <;> omega
  · simp

theorem stemPhysical_endpoints (s : ℕ) (e : Fin (s+4)) :
    (stemPhysicalVertex s (stemEnds s e).1,stemPhysicalVertex s (stemEnds s e).2)=
      Bistar.physicalEnds s 2 0 (stemPhysicalEdge s e) := by
  by_cases h0 : e.val=0
  · simp [stemPhysicalVertex,stemPhysicalEdge,stemEnds,Bistar.physicalEnds,h0]
  by_cases h1 : e.val=1
  · simp [stemPhysicalVertex,stemPhysicalEdge,stemEnds,Bistar.physicalEnds,h1,
      Nat.mod_eq_of_lt (show 2<s+5 by omega)]
  by_cases h2 : e.val=2
  · simp [stemPhysicalVertex,stemPhysicalEdge,stemEnds,Bistar.physicalEnds,h2,
      Nat.mod_eq_of_lt (show 3<s+5 by omega)]
  by_cases h3 : e.val=3
  · simp [stemPhysicalVertex,stemPhysicalEdge,stemEnds,Bistar.physicalEnds,h3,
      Nat.mod_eq_of_lt (show 3<s+5 by omega),Nat.mod_eq_of_lt (show 4<s+5 by omega)]
  by_cases h4 : e.val=4
  · simp [stemPhysicalVertex,stemPhysicalEdge,stemEnds,Bistar.physicalEnds,h4,
      show 4<s+4 by omega,Prod.ext_iff,Fin.ext_iff]
  · simp [stemPhysicalVertex,stemPhysicalEdge,stemEnds,Bistar.physicalEnds,h0,h1,h2,h3,h4,
      show ¬e.val<4 by omega,show ¬e.val<5 by omega,show ¬e.val+1<5 by omega,
      show ¬e.val+1=0 by omega,Prod.ext_iff,Fin.ext_iff]
    omega

theorem physical_to_stem {s : ℕ} {f : Bistar.PhysicalV s 2 0 → ℕ}
    (hf : Complete (s+4) f (Bistar.physicalEnds s 2 0)) :
    Complete (s+4) (f ∘ stemPhysicalVertex s) (stemEnds s) := by
  apply complete_reindex hf _ (stemPhysicalVertex_bijective s) _ (stemPhysicalEdge_bijective s)
  intro e
  have he := stemPhysical_endpoints s e
  have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
  dsimp only at h1 h2; rw [h1,h2]

theorem stem_odd_mark_one_zero (t : ℕ) :
    ∃ f : Fin (2*t+1+5) → ℕ, Complete (2*t+1+4) f (stemEnds (2*t+1)) ∧ f 5=0 := by
  have h := Bistar.odd_physical_complete t 2 0
  have hc := physical_to_stem (by convert h using 1 <;> omega)
  refine ⟨_,complete_reflect hc,?_⟩
  simp [Function.comp_apply,stemPhysicalVertex,Bistar.oddPhysicalLabel,Bistar.oddLabel,Bistar.oddVertex,
    pairLabel,Bistar.label,Nat.mod_eq_of_lt (show 5<2*t+1+5 by omega)]
  omega

end Math15Source10
#print axioms Math15Source10.stem_odd_mark_one_zero
