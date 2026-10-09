import StemBases
import EvenTwoArms

namespace Math15Source10

theorem onePort_step {s : ℕ} (h : OnePort s) : OnePort (s+4) := by
  obtain ⟨k,f,hk,hkm,hc,ha,hr⟩ := h
  refine ⟨k+2,oneTailLabel (s+4) f ∘ growFin (s+5),by omega,by omega,?_,?_,?_⟩
  · exact grow_stem_complete s _ (one_tail_complete hc (stemLeaf s) hr)
  · exact grow_stem_alpha s _ _ (one_tail_alpha ha hk hkm (stemLeaf s) hr)
  · simp [Function.comp_apply,grow_stem_leaf,oneTailLabel]

/-- Every stem length except two has an alpha labeling with the stem port one. -/
theorem onePort_all (s : ℕ) (hs : s≠2) : OnePort s := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hsmall : s<7
    · interval_cases s
      · exact onePort0
      · exact onePort1
      · contradiction
      · exact onePort3
      · exact onePort_step onePort0
      · exact onePort_step onePort1
      · exact onePort6
    · have he : s=s-4+4 := by omega
      have hh := onePort_step (ih (s-4) (by omega) (by omega))
      simpa only [← he] using hh

theorem grow_stem_mark (s : ℕ) (hs : 3≤s) :
    growFin (s+5) (7 : Fin (s+4+5)) = .inl (7 : Fin (s+5)) := by
  simp [growFin,Nat.mod_eq_of_lt (show 7<s+5+4 by omega),
    Nat.mod_eq_of_lt (show 7<s+5 by omega),show 7<s+5 by omega,Fin.ext_iff]

theorem nearPort_step {s : ℕ} (hs : 7≤s) (h : NearPort s) : NearPort (s+4) := by
  obtain ⟨k,f,hk,hkm,hc,ha,hr,hz⟩ := h
  refine ⟨k+2,nearTailLabel (s+4) k f ∘ growFin (s+5),by omega,by omega,?_,?_,?_,?_⟩
  · exact grow_stem_complete s _ (near_tail_complete hc ha (by omega) (stemLeaf s) hr)
  · exact grow_stem_alpha s _ _ (near_tail_alpha hc ha (by omega) (stemLeaf s) hr)
  · simp only [Function.comp_apply,grow_stem_leaf,near_tail_last]
  · simp only [Function.comp_apply,grow_stem_mark s (by omega)]
    rw [near_tail_old hc.2.1 (show k≤s+4 by omega)]
    rcases hz with hz | hz
    · left; simp [hz]
    · right; simp [hz,show ¬s+4≤k by omega]

/-- The exceptional bridge-three family has an extremal marked vertex for
every long-arm length at least seven, with a port suitable for continuation. -/
theorem nearPort_all (s : ℕ) (hs : 7≤s) : NearPort s := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hsmall : s<11
    · have he : s=7 ∨ s=8 ∨ s=9 ∨ s=10 := by omega
      rcases he with rfl | rfl | rfl | rfl
      · exact nearPort7
      · exact nearPort8
      · exact nearPort9
      · exact nearPort10
    · have he : s=s-4+4 := by omega
      have hh := nearPort_step (by omega) (ih (s-4) (by omega) (by omega))
      simpa only [← he] using hh

/-- S(2,2,s), s>=6, is graceful with zero at distance three down its long arm. -/
theorem stem_mark_three_zero (s : ℕ) (hs : 6≤s) :
    ∃ f : Fin (s+5) → ℕ, Complete (s+4) f (stemEnds s) ∧ f 7=0 := by
  by_cases he : s=6
  · subst s; exact markZero6
  · obtain ⟨k,f,hk,hkm,hc,ha,hr,hz⟩ := nearPort_all s (by omega)
    rcases hz with hz | hz
    · exact ⟨f,hc,hz⟩
    · exact ⟨fun v => s+4-f v,complete_reflect hc,by simp [hz]⟩

end Math15Source10
#print axioms Math15Source10.onePort_all
#print axioms Math15Source10.nearPort_all
#print axioms Math15Source10.stem_mark_three_zero
