import PathOne
import CenterTwo
import FixedMarks
import Amalgamation

set_option linter.unusedSimpArgs false
namespace Math15Source10

/-- Literal six-arm model with the two arms at the degree-three vertex fixed
at length two. The other arms have lengths a,b,c+1 and the bridge s+1. -/
abbrev ModelV (a b c s : ℕ) := Fin (s+5) ⊕ (Fin (a+b+1) ⊕ Fin (c+1))
abbrev ModelE (a b c s : ℕ) := Fin (s+4) ⊕ Option (Fin (a+b) ⊕ Option (Fin c))
def modelEnds (a b c s : ℕ) : ModelE a b c s → ModelV a b c s × ModelV a b c s :=
  Math15.Labeling.joinEnds (stemLeaf s) (.inl (pathJunction a b)) (stemEnds s) (spiderEnds a b c)
def ModelGraceful (a b c s : ℕ) : Prop :=
  ∃ f : ModelV a b c s → ℕ, Complete (s+4+(a+b+c+1)+1) f (modelEnds a b c s)
def PathZero (a b : ℕ) : Prop :=
  ∃ (k : ℕ) (f : Fin (a+b+1) → ℕ), k≤a+b ∧ Complete (a+b) f (pathEnds (a+b)) ∧
    Alpha k f (pathEnds (a+b)) ∧ f (pathJunction a b)=0

def modelMark (c s : ℕ) : Fin (s+c+2+5) := ⟨s+5,by omega⟩
def modelWedgeVertex (a b c s : ℕ) : ModelV a b c s →
    Fin (a+b+1) ⊕ {w : Fin (s+c+2+5) // w≠modelMark c s}
  | .inl i => .inr ⟨⟨i.val,by omega⟩,by intro he; have := congrArg Fin.val he; dsimp [modelMark] at this; omega⟩
  | .inr (.inl i) => .inl i
  | .inr (.inr i) => .inr ⟨⟨s+6+i.val,by omega⟩,by intro he; have := congrArg Fin.val he; dsimp [modelMark] at this; omega⟩

def modelWedgeEdge (a b c s : ℕ) : ModelE a b c s → Fin (a+b) ⊕ Fin (s+c+2+4)
  | .inl e => .inr ⟨e.val,by omega⟩
  | .inr none => .inr ⟨s+4,by omega⟩
  | .inr (some (.inl e)) => .inl e
  | .inr (some (.inr none)) => .inr ⟨s+5,by omega⟩
  | .inr (some (.inr (some e))) => .inr ⟨s+6+e.val,by omega⟩

theorem modelWedgeVertex_bijective (a b c s : ℕ) : Function.Bijective (modelWedgeVertex a b c s) := by
  constructor
  · intro x y he
    rcases x with x | x <;> rcases y with y | y
    · simp only [modelWedgeVertex,Sum.inr.injEq,Subtype.mk.injEq,Fin.mk.injEq] at he
      exact congrArg Sum.inl (Fin.ext he)
    · rcases y with y | y
      · simp [modelWedgeVertex] at he
      · have hh := congrArg (fun z => match z with | .inl _ => 0 | .inr w => w.val.val) he
        simp only [modelWedgeVertex] at hh; omega
    · rcases x with x | x
      · simp [modelWedgeVertex] at he
      · have hh := congrArg (fun z => match z with | .inl _ => 0 | .inr w => w.val.val) he
        simp only [modelWedgeVertex] at hh; omega
    · rcases x with x | x <;> rcases y with y | y
      · simpa only [modelWedgeVertex,Sum.inl.injEq] using congrArg Sum.inr (congrArg Sum.inl (Sum.inl.inj he))
      · simp [modelWedgeVertex] at he
      · simp [modelWedgeVertex] at he
      · have hh := congrArg (fun z => match z with | .inl _ => 0 | .inr w => w.val.val) he
        simp only [modelWedgeVertex] at hh
        exact congrArg Sum.inr (congrArg Sum.inr (Fin.ext (by omega)))
  · intro z
    rcases z with z | z
    · exact ⟨.inr (.inl z),rfl⟩
    · have hn : z.val.val≠s+5 := by intro he; exact z.property (Fin.ext he)
      by_cases hz : z.val.val<s+5
      · refine ⟨.inl ⟨z.val.val,hz⟩,?_⟩
        apply congrArg Sum.inr; apply Subtype.ext; apply Fin.ext; rfl
      · refine ⟨.inr (.inr ⟨z.val.val-(s+6),by have := z.val.isLt; omega⟩),?_⟩
        apply congrArg Sum.inr; apply Subtype.ext; apply Fin.ext
        dsimp [modelWedgeVertex]; omega

def modelWedgeEdgeBack (a b c s : ℕ) : Fin (a+b) ⊕ Fin (s+c+2+4) → ModelE a b c s
  | .inl e => .inr (some (.inl e))
  | .inr e => if h : e.val<s+4 then .inl ⟨e.val,h⟩ else
    if h4 : e.val=s+4 then .inr none else if h5 : e.val=s+5 then .inr (some (.inr none)) else
    .inr (some (.inr (some ⟨e.val-(s+6),by omega⟩)))

theorem modelWedgeEdge_left (a b c s : ℕ) :
    Function.LeftInverse (modelWedgeEdgeBack a b c s) (modelWedgeEdge a b c s) := by
  intro e
  rcases e with e | e
  · simp [modelWedgeEdge,modelWedgeEdgeBack,e.isLt]
  · cases e with
    | none => simp [modelWedgeEdge,modelWedgeEdgeBack]
    | some e =>
      rcases e with e | e
      · rfl
      · cases e with
        | none => simp [modelWedgeEdge,modelWedgeEdgeBack]
        | some e =>
          simp [modelWedgeEdge,modelWedgeEdgeBack,show ¬s+6+e.val<s+4 by omega,
            show s+6+e.val≠s+4 by omega,show s+6+e.val≠s+5 by omega,Fin.ext_iff]

theorem modelWedgeEdge_bijective (a b c s : ℕ) : Function.Bijective (modelWedgeEdge a b c s) := by
  apply bijective_of_injective_equal_card _ (modelWedgeEdge_left a b c s).injective
  simp; omega

theorem modelWedge_endpoints (a b c s : ℕ) (e : ModelE a b c s) :
    (modelWedgeVertex a b c s (modelEnds a b c s e).1,
     modelWedgeVertex a b c s (modelEnds a b c s e).2)=
    wedgeEnds (pathJunction a b) (modelMark c s) (pathEnds (a+b)) (stemEnds (s+c+2))
      (modelWedgeEdge a b c s e) := by
  rcases e with e | e
  · by_cases h0 : e.val=0
    · simp [modelEnds,Math15.Labeling.joinEnds,modelWedgeVertex,modelWedgeEdge,wedgeEnds,
        wedgeVertex,stemEnds,modelMark,h0,Fin.ext_iff]
    by_cases h1 : e.val=1
    · simp [modelEnds,Math15.Labeling.joinEnds,modelWedgeVertex,modelWedgeEdge,wedgeEnds,
        wedgeVertex,stemEnds,modelMark,h1,Fin.ext_iff,
        Nat.mod_eq_of_lt (show 2<s+5 by omega),Nat.mod_eq_of_lt (show 2<s+c+2+5 by omega)]
    by_cases h2 : e.val=2
    · simp [modelEnds,Math15.Labeling.joinEnds,modelWedgeVertex,modelWedgeEdge,wedgeEnds,
        wedgeVertex,stemEnds,modelMark,h2,Fin.ext_iff,
        Nat.mod_eq_of_lt (show 3<s+5 by omega),Nat.mod_eq_of_lt (show 3<s+c+2+5 by omega)]
    by_cases h3 : e.val=3
    · simp [modelEnds,Math15.Labeling.joinEnds,modelWedgeVertex,modelWedgeEdge,wedgeEnds,
        wedgeVertex,stemEnds,modelMark,h3,Fin.ext_iff,
        Nat.mod_eq_of_lt (show 3<s+5 by omega),Nat.mod_eq_of_lt (show 3<s+c+2+5 by omega),
        Nat.mod_eq_of_lt (show 4<s+5 by omega),Nat.mod_eq_of_lt (show 4<s+c+2+5 by omega)]
    by_cases h4 : e.val=4
    · simp [modelEnds,Math15.Labeling.joinEnds,modelWedgeVertex,modelWedgeEdge,wedgeEnds,
        wedgeVertex,stemEnds,modelMark,h4,Fin.ext_iff,show 0<s by omega,show s≠0 by omega]
    · simp [modelEnds,Math15.Labeling.joinEnds,modelWedgeVertex,modelWedgeEdge,wedgeEnds,
        wedgeVertex,stemEnds,modelMark,h0,h1,h2,h3,h4,Fin.ext_iff,
        show e.val≠s+5 by omega,show e.val+1≠s+5 by omega,show e.val≠s+4 by omega]
  · cases e with
    | none =>
      by_cases hs : s=0
      · subst s
        simp [modelEnds,Math15.Labeling.joinEnds,modelWedgeVertex,modelWedgeEdge,wedgeEnds,
          wedgeVertex,stemEnds,stemLeaf,modelMark,Fin.ext_iff]
      · simp [modelEnds,Math15.Labeling.joinEnds,modelWedgeVertex,modelWedgeEdge,wedgeEnds,
          wedgeVertex,stemEnds,stemLeaf,modelMark,hs,Fin.ext_iff,
          show s+4≠0 by omega,show s+4≠1 by omega,show s+4≠2 by omega,
          show s+4≠3 by omega,show s+4≠4 by omega]
    | some e =>
      rcases e with e | e
      · rfl
      · cases e with
        | none =>
          simp [modelEnds,spiderEnds,Math15.Labeling.joinEnds,modelWedgeVertex,modelWedgeEdge,wedgeEnds,
            wedgeVertex,stemEnds,modelMark,Fin.ext_iff,
            show s+5≠0 by omega,show s+5≠1 by omega,show s+5≠2 by omega,
            show s+5≠3 by omega,show s+5≠4 by omega]
        | some e =>
          simp [modelEnds,spiderEnds,Math15.Labeling.joinEnds,modelWedgeVertex,modelWedgeEdge,wedgeEnds,
            wedgeVertex,stemEnds,modelMark,pathEnds,Fin.ext_iff,
            show s+6+e.val≠0 by omega,show s+6+e.val≠1 by omega,
            show s+6+e.val≠2 by omega,show s+6+e.val≠3 by omega,
            show s+6+e.val≠4 by omega,show s+6+e.val≠s+5 by omega,
            show s+6+e.val+1≠s+5 by omega]
          simp only [Nat.add_assoc,Fin.ext_iff,Subtype.mk.injEq,Sum.inr.injEq,Prod.mk.injEq]
          simp [show 6+e.val≠4 by omega]

theorem model_of_markzero {a b c s : ℕ} (hp : PathZero a b)
    (hm : MarkZero (s+c+2) (s+5)) : ModelGraceful a b c s := by
  obtain ⟨k,f,hk,hf,ha,hr⟩ := hp
  obtain ⟨g,hg,hgr⟩ := hm
  obtain ⟨F,hF⟩ := wedge_zero_complete hf hg ha hk (pathJunction a b) (modelMark c s) hr
    (hgr (modelMark c s) rfl)
  refine ⟨F ∘ modelWedgeVertex a b c s,?_⟩
  have hh := complete_reindex hF _ (modelWedgeVertex_bijective a b c s)
    _ (modelWedgeEdge_bijective a b c s) (modelEnds a b c s) (by
      intro e
      have he := modelWedge_endpoints a b c s e
      have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
      dsimp only at h1 h2; rw [h1,h2])
  convert hh using 1 <;> omega

theorem model_one {a b c s : ℕ} (ha : 3≤a) (hb : a≤b) (hc : b≤c+1)
    (hex : a≠4 ∨ b≠4) (hs : s≠2) : ModelGraceful a b c s := by
  obtain ⟨f,hf,hr⟩ := spider_center_one_except44 a b c ha hb hc hex
  exact join_stem_to_one hf (.inl (pathJunction a b)) hr s hs

theorem pathZero44 : PathZero 4 4 := by
  refine ⟨4,![1,6,2,8,0,7,4,5,3],by decide,?_,by unfold Alpha; decide,by decide⟩
  exact complete_finite _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem model44_all (c s : ℕ) (hc : 3≤c) : ModelGraceful 4 4 c s := by
  by_cases hs : 3≤s ∧ s≠5
  · obtain ⟨f,hf,hr⟩ := spider44_center_two c (by omega)
    exact join_stem_to_two hf (.inl (pathJunction 4 4)) hr s hs.1 hs.2
  · apply model_of_markzero pathZero44
    have he : s=0 ∨ s=1 ∨ s=2 ∨ s=5 := by omega
    rcases he with rfl | rfl | rfl | rfl
    · exact stem_mark_one_zero _ (by omega)
    · exact stem_mark_two_zero _ (by omega)
    · obtain ⟨f,hf,hr⟩ := stem_mark_three_zero (2+c+2) (by omega)
      refine ⟨f,hf,?_⟩
      intro v hv
      have he : v=7 := Fin.ext (by simpa [Nat.mod_eq_of_lt (show 7<2+c+2+5 by omega)] using hv)
      simpa only [he] using hr
    · exact stem_mark_six_zero _ (by omega)

end Math15Source10
#print axioms Math15Source10.model_of_markzero
#print axioms Math15Source10.model_one
#print axioms Math15Source10.model44_all
