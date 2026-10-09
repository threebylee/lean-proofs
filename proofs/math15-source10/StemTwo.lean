import AlphaTailTwo

namespace Math15Source10

def growEightFin (n : ℕ) (i : Fin (n+8)) : Fin n ⊕ Fin 8 :=
  if h : i.val<n then .inl ⟨i.val,h⟩ else .inr ⟨i.val-n,by omega⟩

theorem growEightFin_injective (n : ℕ) : Function.Injective (growEightFin n) := by
  intro i j he
  apply Fin.ext
  simp only [growEightFin] at he
  split_ifs at he <;> simp_all [Fin.ext_iff] <;> omega

theorem growEightFin_bijective (n : ℕ) : Function.Bijective (growEightFin n) := by
  apply bijective_of_injective_equal_card _ (growEightFin_injective n)
  simp

/-- Exact endpoint correspondence for extending the stem by four edges. -/
theorem grow_eight_stem_ends (s : ℕ) (e : Fin (s+4+8)) :
    (growEightFin (s+5) (stemEnds (s+8) e).1,growEightFin (s+5) (stemEnds (s+8) e).2) =
      tailEightEnds (stemEnds s) (stemLeaf s) (growEightFin (s+4) e) := by
  by_cases h0 : e.val=0
  · simp [stemEnds,growEightFin,tailEightEnds,h0]
  by_cases h1 : e.val=1
  · simp [stemEnds,growEightFin,tailEightEnds,h1,Nat.mod_eq_of_lt (show 2<s+5+8 by omega),show 2<s+5 by omega,Fin.ext_iff,Nat.mod_eq_of_lt (show 2<s+5 by omega)]
  by_cases h2 : e.val=2
  · simp [stemEnds,growEightFin,tailEightEnds,h2,Nat.mod_eq_of_lt (show 3<s+5+8 by omega),show 3<s+5 by omega,Fin.ext_iff,Nat.mod_eq_of_lt (show 3<s+5 by omega)]
  by_cases h3 : e.val=3
  · simp [stemEnds,growEightFin,tailEightEnds,h3,Nat.mod_eq_of_lt (show 3<s+5+8 by omega),Nat.mod_eq_of_lt (show 4<s+5+8 by omega),show 3<s+5 by omega,show 4<s+5 by omega,Fin.ext_iff,Nat.mod_eq_of_lt (show 3<s+5 by omega),Nat.mod_eq_of_lt (show 4<s+5 by omega)]
  by_cases ho : e.val<s+4
  · have hv : e.val<s+5 := by omega
    have hw : e.val+1<s+5 := by omega
    by_cases h4 : e.val=4
    · simp [stemEnds,growEightFin,tailEightEnds,h4,show 0<s by omega]
    · simp [stemEnds,growEightFin,tailEightEnds,h0,h1,h2,h3,h4,ho,hv,hw]
  · have he : e.val=s+4 ∨ e.val=s+5 ∨ e.val=s+6 ∨ e.val=s+7 ∨
        e.val=s+8 ∨ e.val=s+9 ∨ e.val=s+10 ∨ e.val=s+11 := by omega
    rcases he with he | he | he | he | he | he | he | he
    · by_cases hs : s=0
      · subst s; simp [stemEnds,growEightFin,tailEightEnds,stemLeaf,he]
      · simp [stemEnds,growEightFin,tailEightEnds,stemLeaf,he,hs,Fin.ext_iff]
    all_goals simp [stemEnds,growEightFin,tailEightEnds,he,Fin.ext_iff]

/-- Reindex the attached tail onto the direct Fin-indexed stem graph. -/
theorem grow_eight_stem_complete (s : ℕ) (f : Fin (s+5) ⊕ Fin 8 → ℕ)
    (h : Complete (s+4+8) f (tailEightEnds (stemEnds s) (stemLeaf s))) :
    Complete (s+4+8) (f ∘ growEightFin (s+5)) (stemEnds (s+8)) := by
  apply complete_reindex h _ (growEightFin_bijective _) _ (growEightFin_bijective _)
  intro e
  have hh := grow_eight_stem_ends s e
  have h1 := congrArg Prod.fst hh
  have h2 := congrArg Prod.snd hh
  dsimp only at h1 h2
  rw [h1,h2]

theorem grow_eight_stem_alpha (s k : ℕ) (f : Fin (s+5) ⊕ Fin 8 → ℕ)
    (h : Alpha k f (tailEightEnds (stemEnds s) (stemLeaf s))) :
    Alpha k (f ∘ growEightFin (s+5)) (stemEnds (s+8)) := by
  intro e
  have hh := h (growEightFin (s+4) e)
  have he := grow_eight_stem_ends s e
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp only [Function.comp_apply] at h1 h2 ⊢
  rw [h1,h2]
  exact hh

theorem grow_eight_stem_leaf (s : ℕ) : growEightFin (s+5) (stemLeaf (s+8)) = .inr 7 := by
  simp [growEightFin,stemLeaf,show s+8≠0 by omega,show ¬s+4+8<s+5 by omega,Fin.ext_iff]


def TwoPort (s : ℕ) : Prop :=
  ∃ (k : ℕ) (f : Fin (s+5) → ℕ), 2≤k ∧ k≤s+4 ∧
    Complete (s+4) f (stemEnds s) ∧ Alpha k f (stemEnds s) ∧ f (stemLeaf s)=2

theorem twoPort3 : TwoPort 3 := by
  refine ⟨3,![6,0,7,1,5,3,4,2],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem twoPort4 : TwoPort 4 := by
  refine ⟨4,![1,8,0,7,3,6,4,5,2],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem twoPort6 : TwoPort 6 := by
  refine ⟨5,![1,10,0,8,4,9,3,6,5,7,2],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem twoPort7 : TwoPort 7 := by
  refine ⟨5,![11,0,9,3,10,1,6,5,7,4,8,2],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem twoPort8 : TwoPort 8 := by
  refine ⟨6,![0,12,1,10,3,8,4,9,6,7,5,11,2],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem twoPort9 : TwoPort 9 := by
  refine ⟨6,![13,0,10,1,12,4,11,3,9,5,8,6,7,2],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem twoPort10 : TwoPort 10 := by
  refine ⟨7,![0,14,1,12,4,9,5,11,6,8,7,10,3,13,2],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem twoPort13 : TwoPort 13 := by
  refine ⟨8,![17,0,15,1,13,3,16,5,14,4,12,6,11,7,10,8,9,2],by decide,by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem twoPort_step {s : ℕ} (h : TwoPort s) : TwoPort (s+8) := by
  obtain ⟨k,f,hk,hkm,hc,ha,hr⟩ := h
  refine ⟨k+4,twoTailLabel (s+4) f ∘ growEightFin (s+5),by omega,by omega,?_,?_,?_⟩
  · exact grow_eight_stem_complete s _ (two_tail_complete hc (stemLeaf s) hr)
  · exact grow_eight_stem_alpha s _ _ (two_tail_alpha ha hk hkm (stemLeaf s) hr)
  · simp [Function.comp_apply,grow_eight_stem_leaf,twoTailLabel]

theorem twoPort_all (s : ℕ) (hs : 3≤s) (h5 : s≠5) : TwoPort s := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hsmall : s<14
    · interval_cases s <;> first
        | omega
        | exact twoPort3
        | exact twoPort4
        | exact twoPort6
        | exact twoPort7
        | exact twoPort8
        | exact twoPort9
        | exact twoPort10
        | exact twoPort13
        | exact twoPort_step twoPort3
        | exact twoPort_step twoPort4
    · have he : s=s-8+8 := by omega
      have hh := twoPort_step (ih (s-8) (by omega) (by omega) (by omega))
      simpa only [← he] using hh

end Math15Source10
#print axioms Math15Source10.twoPort_all
