import StemLeafZero
import PathZeroBalanced

set_option linter.unusedSimpArgs false
namespace Math15Source10

theorem complete_of_good_card {V E : Type*} [Fintype V] {m : ℕ}
    {f : V → ℕ} {ends : E → V × V} (h : Math15.Labeling.Good m f ends)
    (hc : Fintype.card V=m+1) : Complete m f ends := by
  refine ⟨h.1,h.2.1,?_,h.2.2.1,h.2.2.2⟩
  let ff : V → Fin (m+1) := fun v => ⟨f v,by have := h.2.1 v; omega⟩
  have hb : Function.Bijective ff := by
    apply bijective_of_injective_equal_card
    · intro v w he; exact h.1 (congrArg Fin.val he)
    · simpa using hc
  intro d hd
  obtain ⟨v,hv⟩ := hb.2 ⟨d,by omega⟩
  exact ⟨v,congrArg Fin.val hv⟩

def growOneVertex (s : ℕ) (v : Fin (s+1+5)) : Option (Fin (s+5)) :=
  if h : v.val<s+5 then some ⟨v.val,h⟩ else none
def growOneEdge (s : ℕ) (e : Fin (s+1+4)) : Option (Fin (s+4)) :=
  if h : e.val<s+4 then some ⟨e.val,h⟩ else none

theorem growOneVertex_bijective (s : ℕ) : Function.Bijective (growOneVertex s) := by
  apply bijective_of_injective_equal_card
  · intro v w he
    apply Fin.ext
    simp only [growOneVertex] at he
    split_ifs at he <;> simp_all [Fin.ext_iff] <;> omega
  · simp

theorem growOneEdge_bijective (s : ℕ) : Function.Bijective (growOneEdge s) := by
  apply bijective_of_injective_equal_card
  · intro v w he
    apply Fin.ext
    simp only [growOneEdge] at he
    split_ifs at he <;> simp_all [Fin.ext_iff] <;> omega
  · simp

theorem growOne_endpoints (s : ℕ) (hs : 1≤s) (e : Fin (s+1+4)) :
    (growOneVertex s (stemEnds (s+1) e).1,growOneVertex s (stemEnds (s+1) e).2)=
      Math15.Labeling.leafEnds (stemLeaf s) (stemEnds s) (growOneEdge s e) ∨
    (growOneVertex s (stemEnds (s+1) e).2,growOneVertex s (stemEnds (s+1) e).1)=
      Math15.Labeling.leafEnds (stemLeaf s) (stemEnds s) (growOneEdge s e) := by
  by_cases he : e.val<s+4
  · left
    by_cases h0 : e.val=0
    · simp [Fin.ext_iff,growOneEdge,growOneVertex,Math15.Labeling.leafEnds,stemEnds,h0]
    by_cases h1 : e.val=1
    · simp [Fin.ext_iff,growOneEdge,growOneVertex,Math15.Labeling.leafEnds,stemEnds,h1,
        Nat.mod_eq_of_lt (show 2<s+5 by omega),Nat.mod_eq_of_lt (show 2<s+1+5 by omega),
        show 2<s+5 by omega]
    by_cases h2 : e.val=2
    · simp [Fin.ext_iff,growOneEdge,growOneVertex,Math15.Labeling.leafEnds,stemEnds,h2,
        Nat.mod_eq_of_lt (show 3<s+5 by omega),Nat.mod_eq_of_lt (show 3<s+1+5 by omega),
        show 3<s+5 by omega,show 2<s+4 by omega]
    by_cases h3 : e.val=3
    · simp [Fin.ext_iff,growOneEdge,growOneVertex,Math15.Labeling.leafEnds,stemEnds,h3,
        Nat.mod_eq_of_lt (show 3<s+5 by omega),Nat.mod_eq_of_lt (show 3<s+1+5 by omega),
        Nat.mod_eq_of_lt (show 4<s+5 by omega),Nat.mod_eq_of_lt (show 4<s+1+5 by omega),
        show 3<s+5 by omega,show 4<s+5 by omega,show 3<s+4 by omega]
    by_cases h4 : e.val=4
    · simp [Fin.ext_iff,growOneEdge,growOneVertex,Math15.Labeling.leafEnds,stemEnds,h4,
        show 4<s+4 by omega,show 5<s+5 by omega]
    · simp [Fin.ext_iff,growOneEdge,growOneVertex,Math15.Labeling.leafEnds,stemEnds,h0,h1,h2,h3,h4,he,
        show e.val<s+5 by omega,show e.val+1<s+5 by omega]
  · have hv : e.val=s+4 := by omega
    right
    simp [growOneEdge,growOneVertex,stemEnds,stemLeaf,Math15.Labeling.leafEnds,hv,
      show s≠0 by omega,show s+4≠0 by omega,show s+4≠1 by omega,
      show s+4≠2 by omega,show s+4≠3 by omega,show s+4≠4 by omega,
      Prod.ext_iff,Fin.ext_iff]

theorem stem_one_before_end_zero (s : ℕ) (hs : 1≤s) : MarkZero (s+1) (s+4) := by
  obtain ⟨f,hf,hr⟩ := stem_leaf_zero s
  have hh := complete_of_good_card (Math15.Labeling.add_leaf hf.good (stemLeaf s) hr)
    (by simp)
  have hg := complete_reflect hh
  refine ⟨(fun v => s+4+1-Math15.Labeling.leafLabel (s+4) f v) ∘ growOneVertex s,?_,?_⟩
  · apply complete_reindex (show Complete (s+1+4) _ _ by simpa using hg)
      _ (growOneVertex_bijective s) _ (growOneEdge_bijective s)
    intro e
    rcases growOne_endpoints s hs e with he | he
    · have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
      dsimp only at h1 h2; rw [h1,h2]
    · have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
      dsimp only at h1 h2; rw [h1,h2,Nat.dist_comm]
  · intro v hv
    have he : growOneVertex s v=some (stemLeaf s) := by
      simp [growOneVertex,hv,stemLeaf,show s≠0 by omega]
    simp only [Function.comp_apply,he,Math15.Labeling.leafLabel,hr,Nat.sub_zero,Nat.sub_self]

theorem model_short_one {a b s : ℕ} (ha : 1≤a) (hb : 1≤b) (hex : a≠2 ∨ b≠2) :
    ModelGraceful a b 0 s := by
  apply model_of_markzero (pathZero_all a b ha hb hex)
  convert stem_one_before_end_zero (s+1) (by omega) using 1 <;> omega

end Math15Source10
#print axioms Math15Source10.stem_one_before_end_zero
#print axioms Math15Source10.model_short_one
