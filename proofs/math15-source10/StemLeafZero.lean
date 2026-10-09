import Stem

namespace Math15Source10

/-- The two short arms use the four labels immediately above s/2;
the stem alternates downwards and upwards from that interval. -/
def leafRaw (s : ℕ) (v : Fin (s+5)) : ℕ :=
  if v.val=0 then s/2 else
  if v.val=1 then s/2+4 else
  if v.val=2 then s/2+1 else
  if v.val=3 then s/2+2 else
  if v.val=4 then s/2+3 else
  if (v.val-4)%2=0 then s/2-(v.val-4)/2 else s/2+5+(v.val-4)/2

theorem leafRaw_dist (s : ℕ) (e : Fin (s+4)) :
    Nat.dist (leafRaw s (stemEnds s e).1) (leafRaw s (stemEnds s e).2)=
      if e.val<4 then 4-e.val else e.val+1 := by
  by_cases h0 : e.val=0
  · simp [stemEnds,leafRaw,h0,Nat.dist]
  by_cases h1 : e.val=1
  · simp [stemEnds,leafRaw,h1,Nat.dist,Nat.mod_eq_of_lt (show 2<s+5 by omega)]
  by_cases h2 : e.val=2
  · simp [stemEnds,leafRaw,h2,Nat.dist,Nat.mod_eq_of_lt (show 3<s+5 by omega)]
  by_cases h3 : e.val=3
  · simp [stemEnds,leafRaw,h3,Nat.dist,Nat.mod_eq_of_lt (show 3<s+5 by omega),
      Nat.mod_eq_of_lt (show 4<s+5 by omega)]
  by_cases h4 : e.val=4
  · simp [stemEnds,leafRaw,h4,Nat.dist]
  · simp only [stemEnds,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,
      leafRaw,show ¬e.val<4 by omega]
    have he := e.isLt
    split_ifs <;> simp only [Fin.val_mk,Nat.dist] <;> first | contradiction | omega

set_option maxHeartbeats 800000 in
theorem leafRaw_complete (s : ℕ) : Complete (s+4) (leafRaw s) (stemEnds s) := by
  apply complete_finite _ _ _ (by simp) (by simp)
  · intro v w he
    apply Fin.ext
    simp only [leafRaw] at he
    split_ifs at he <;> omega
  · intro v
    simp only [leafRaw]
    split_ifs <;> omega
  · intro e
    rw [leafRaw_dist]
    split_ifs <;> omega
  · intro e g he
    dsimp only at he
    rw [leafRaw_dist,leafRaw_dist] at he
    apply Fin.ext
    split_ifs at he <;> omega

theorem leafRaw_end (s : ℕ) : leafRaw s (stemLeaf s)=0 ∨ leafRaw s (stemLeaf s)=s+4 := by
  by_cases hs : s=0
  · subst s; left; decide
  · simp only [stemLeaf,if_neg hs,leafRaw,Fin.val_mk]
    split_ifs <;> first | contradiction | omega

theorem stem_leaf_zero (s : ℕ) : ∃ f : Fin (s+5) → ℕ,
    Complete (s+4) f (stemEnds s) ∧ f (stemLeaf s)=0 := by
  rcases leafRaw_end s with h | h
  · exact ⟨leafRaw s,leafRaw_complete s,h⟩
  · refine ⟨fun v => s+4-leafRaw s v,complete_reflect (leafRaw_complete s),?_⟩
    simp only [h,Nat.sub_self]

end Math15Source10
#print axioms Math15Source10.stem_leaf_zero
