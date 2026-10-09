import RegularAssembly

set_option linter.unusedSimpArgs false
namespace Math15Source10

def regular22Vertex (a b c s : ℕ) : RegularV a b c (s+1) 2 2 → ModelV a b c s
  | .inl i => .inl ⟨if i.val≤2 then 2-i.val else i.val,by split_ifs <;> omega⟩
  | .inr ⟨.inl j,_⟩ => if h : j.val=0 then .inr (.inl (pathJunction a b))
      else .inl ⟨s+5-j.val,by omega⟩
  | .inr ⟨.inr j,_⟩ => .inr j.val

def regular22Back (a b c s : ℕ) : ModelV a b c s → RegularV a b c (s+1) 2 2
  | .inl i => if h : i.val<5 then .inl ⟨if i.val≤2 then 2-i.val else i.val,by split_ifs <;> omega⟩
      else .inr ⟨.inl ⟨s+5-i.val,by omega⟩,by
        intro he; have hh := congrArg (fun z : FourV a b c (s+1) => match z with | .inl j => j.val | .inr _ => 0) he
        simp [fourLeaf] at hh; omega⟩
  | .inr y => .inr ⟨wedgeVertex (0 : Fin (s+1+1)) (spiderRoot a b c) y,by
      simp only [wedgeVertex]; split_ifs <;> simp [fourLeaf,Fin.ext_iff]⟩

theorem regular22Vertex_left (a b c s : ℕ) :
    Function.LeftInverse (regular22Back a b c s) (regular22Vertex a b c s) := by
  intro v
  rcases v with i | ⟨w,hw⟩
  · fin_cases i <;> simp [regular22Vertex,regular22Back]
  · rcases w with j | y
    · have hj : j.val≠s+1 := by intro he; exact hw (congrArg Sum.inl (Fin.ext he))
      by_cases h0 : j.val=0
      · have hj0 : j=0 := Fin.ext h0
        subst j
        simp [regular22Vertex,regular22Back,wedgeVertex,spiderRoot,Subtype.ext_iff,Fin.ext_iff]
      · simp [regular22Vertex,regular22Back,h0,show ¬s+5-j.val<5 by omega,
          Subtype.ext_iff,Fin.ext_iff]
        omega
    · simp [regular22Vertex,regular22Back,wedgeVertex,y.property]

def regular22Edge (a b c s : ℕ) : RegularE a b c (s+1) 2 2 → ModelE a b c s
  | .inl i => .inl ⟨if i.val<2 then 1-i.val else i.val,by split_ifs <;> omega⟩
  | .inr (.inl j) => if h : j.val=0 then .inr none else .inl ⟨s+4-j.val,by omega⟩
  | .inr (.inr e) => .inr (some e)

def regular22EdgeBack (a b c s : ℕ) : ModelE a b c s → RegularE a b c (s+1) 2 2
  | .inl i => if h : i.val<4 then .inl ⟨if i.val<2 then 1-i.val else i.val,by split_ifs <;> omega⟩
      else .inr (.inl ⟨s+4-i.val,by omega⟩)
  | .inr none => .inr (.inl 0)
  | .inr (some e) => .inr (.inr e)

theorem regular22Edge_left (a b c s : ℕ) :
    Function.LeftInverse (regular22EdgeBack a b c s) (regular22Edge a b c s) := by
  intro e
  rcases e with i | e
  · fin_cases i <;> simp [regular22Edge,regular22EdgeBack]
  · rcases e with j | e
    · by_cases h0 : j.val=0
      · have hj0 : j=0 := Fin.ext h0
        subst j; simp [regular22Edge,regular22EdgeBack]
      · simp [regular22Edge,regular22EdgeBack,h0,show ¬s+4-j.val<4 by omega,Fin.ext_iff]
        omega
    · rfl

theorem regular22Vertex_bijective (a b c s : ℕ) : Function.Bijective (regular22Vertex a b c s) := by
  apply bijective_of_injective_equal_card _ (regular22Vertex_left a b c s).injective
  simp only [RegularV,FourV,SpiderV,ModelV,Fintype.card_sum,Fintype.card_fin,
    Fintype.card_subtype_compl,Fintype.card_subtype_eq]
  omega

theorem regular22Edge_bijective (a b c s : ℕ) : Function.Bijective (regular22Edge a b c s) := by
  apply bijective_of_injective_equal_card _ (regular22Edge_left a b c s).injective
  simp [RegularE,FourE,SpiderE,ModelE]; omega

theorem regular22_spider_vertex (a b c s : ℕ) (x : SpiderV a b c) :
    regular22Vertex a b c s
      (wedgeVertex (pathJunction 2 2) (fourLeaf a b c (s+1))
        (wedgeVertex (0 : Fin (s+1+1)) (spiderRoot a b c) x)) = .inr x := by
  by_cases hx : x=spiderRoot a b c
  · subst x
    simp [wedgeVertex,fourLeaf,Fin.ext_iff,regular22Vertex,spiderRoot]
  · simp [wedgeVertex,hx,fourLeaf,regular22Vertex]

theorem regular22_endpoints (a b c s : ℕ) (e : RegularE a b c (s+1) 2 2) :
    (regular22Vertex a b c s (regularEnds a b c (s+1) 2 2 e).1,
      regular22Vertex a b c s (regularEnds a b c (s+1) 2 2 e).2)=
      modelEnds a b c s (regular22Edge a b c s e) ∨
    (regular22Vertex a b c s (regularEnds a b c (s+1) 2 2 e).1,
      regular22Vertex a b c s (regularEnds a b c (s+1) 2 2 e).2)=
      ((modelEnds a b c s (regular22Edge a b c s e)).2,
       (modelEnds a b c s (regular22Edge a b c s e)).1) := by
  rcases e with i | e
  · fin_cases i <;> simp [regularEnds,wedgeEnds,pathEnds,regular22Vertex,regular22Edge,
      modelEnds,Math15.Labeling.joinEnds,stemEnds,Prod.ext_iff,Fin.ext_iff,
      Nat.mod_eq_of_lt (show 2<s+5 by omega),Nat.mod_eq_of_lt (show 3<s+5 by omega),
      Nat.mod_eq_of_lt (show 4<s+5 by omega)]
  · rcases e with j | e
    · right
      by_cases hj0 : j.val=0
      · by_cases hs : s=0
        · subst s
          have hj : j=0 := Fin.ext hj0
          subst j
          simp [regularEnds,wedgeEnds,fourEnds,pathEnds,wedgeVertex,regular22Vertex,regular22Edge,
            fourLeaf,modelEnds,Math15.Labeling.joinEnds,stemLeaf,stemEnds,spiderRoot,pathJunction]
        · simp [regularEnds,wedgeEnds,fourEnds,pathEnds,wedgeVertex,regular22Vertex,regular22Edge,
            fourLeaf,modelEnds,Math15.Labeling.joinEnds,stemLeaf,stemEnds,spiderRoot,pathJunction,hj0,hs,
            Prod.ext_iff,Subtype.ext_iff,Fin.ext_iff]
      · by_cases hjlast : j.val=s
        · simp [regularEnds,wedgeEnds,fourEnds,pathEnds,wedgeVertex,regular22Vertex,regular22Edge,
            fourLeaf,modelEnds,Math15.Labeling.joinEnds,stemLeaf,stemEnds,spiderRoot,pathJunction,hjlast,
            show s≠0 by omega,Prod.ext_iff,Subtype.ext_iff,Fin.ext_iff]
        · simp [regularEnds,wedgeEnds,fourEnds,pathEnds,wedgeVertex,regular22Vertex,regular22Edge,
            fourLeaf,modelEnds,Math15.Labeling.joinEnds,stemLeaf,stemEnds,spiderRoot,pathJunction,hj0,hjlast,
            show j.val≠s+1 by omega,show j.val+1≠s+1 by omega,show j.val+1≠0 by omega,
            show s+4-j.val≠0 by omega,show s+4-j.val≠1 by omega,show s+4-j.val≠2 by omega,
            show s+4-j.val≠3 by omega,show s+4-j.val≠4 by omega,
            Prod.ext_iff,Subtype.ext_iff,Fin.ext_iff]
          omega
    · left
      simp only [regularEnds,wedgeEnds,fourEnds,regular22Edge,modelEnds,Math15.Labeling.joinEnds]
      exact Prod.ext (regular22_spider_vertex a b c s _) (regular22_spider_vertex a b c s _)

/-- The exceptional and regular constructions describe the same literal
six-arm tree when the two right arms both have length two. -/
theorem model_to_regular22 {a b c s : ℕ} (h : ModelGraceful a b c s) :
    ∃ F : RegularV a b c (s+1) 2 2 → ℕ,
      Complete (2+2+(s+1+(a+b+c+1))) F (regularEnds a b c (s+1) 2 2) := by
  obtain ⟨f,hf⟩ := h
  have hh := complete_reindex hf _ (regular22Vertex_bijective a b c s) _ (regular22Edge_bijective a b c s)
    (regularEnds a b c (s+1) 2 2) (by
      intro e
      rcases regular22_endpoints a b c s e with h | h
      · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
        dsimp only at h1 h2; rw [h1,h2]
      · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
        dsimp only at h1 h2; rw [h1,h2,Nat.dist_comm])
  refine ⟨f ∘ regular22Vertex a b c s,?_⟩
  convert hh using 1 <;> omega

end Math15Source10
#print axioms Math15Source10.model_to_regular22
