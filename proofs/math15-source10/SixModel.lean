import RegularExceptional
import TreeEmbedding

set_option linter.unusedSimpArgs false
namespace Math15Source10

abbrev ArmsV (a b c e f : ℕ) := Fin a ⊕ (Fin b ⊕ (Fin c ⊕ (Fin e ⊕ Fin f)))
abbrev SixV (a b c d e f : ℕ) := Fin (d+1) ⊕ ArmsV a b c e f
abbrev SixE (a b c d e f : ℕ) := Fin d ⊕ ArmsV a b c e f

def armEnds {V : Type*} {k : ℕ} (root : V) (arm : Fin k → V) (i : Fin k) : V × V :=
  (if h : i.val=0 then root else arm ⟨i.val-1,by omega⟩,arm i)

def sixEnds (a b c d e f : ℕ) : SixE a b c d e f → SixV a b c d e f × SixV a b c d e f
  | .inl i => (.inl ⟨i.val,by omega⟩,.inl ⟨i.val+1,by omega⟩)
  | .inr (.inl i) => armEnds (.inl 0) (fun j => .inr (.inl j)) i
  | .inr (.inr (.inl i)) => armEnds (.inl 0) (fun j => .inr (.inr (.inl j))) i
  | .inr (.inr (.inr (.inl i))) => armEnds (.inl 0) (fun j => .inr (.inr (.inr (.inl j)))) i
  | .inr (.inr (.inr (.inr (.inl i)))) =>
      armEnds (.inl ⟨d,by omega⟩) (fun j => .inr (.inr (.inr (.inr (.inl j))))) i
  | .inr (.inr (.inr (.inr (.inr i)))) =>
      armEnds (.inl ⟨d,by omega⟩) (fun j => .inr (.inr (.inr (.inr (.inr j))))) i

def regularSixVertex (a b c d e f : ℕ) : RegularV a b c d e f → SixV a b (c+1) d e f
  | .inl i => if h : i.val<e then .inr (.inr (.inr (.inr (.inl ⟨e-1-i.val,by omega⟩))))
      else if he : i.val=e then .inl ⟨d,by omega⟩
      else .inr (.inr (.inr (.inr (.inr ⟨i.val-e-1,by omega⟩))))
  | .inr ⟨.inl j,_⟩ => .inl j
  | .inr ⟨.inr ⟨.inl j,_⟩,_⟩ =>
      if h : j.val<a then .inr (.inl ⟨a-1-j.val,by omega⟩)
      else .inr (.inr (.inl ⟨j.val-a-1,by
        have hj : j.val≠a := by
          intro he; rename_i hn _
          exact hn (congrArg Sum.inl (Fin.ext he))
        omega⟩))
  | .inr ⟨.inr ⟨.inr j,_⟩,_⟩ => .inr (.inr (.inr (.inl j)))

def regularSixBack (a b c d e f : ℕ) : SixV a b (c+1) d e f → RegularV a b c d e f
  | .inl j => if h : j.val=d then .inl (pathJunction e f)
      else .inr ⟨.inl j,by simpa [fourLeaf,Fin.ext_iff] using h⟩
  | .inr (.inl i) => .inr ⟨.inr ⟨.inl ⟨a-1-i.val,by omega⟩,by
      simp [spiderRoot,pathJunction,Fin.ext_iff]; omega⟩,by simp [fourLeaf]⟩
  | .inr (.inr (.inl i)) => .inr ⟨.inr ⟨.inl ⟨a+i.val+1,by omega⟩,by
      simp [spiderRoot,pathJunction,Fin.ext_iff]; omega⟩,by simp [fourLeaf]⟩
  | .inr (.inr (.inr (.inl i))) => .inr ⟨.inr ⟨.inr i,by simp [spiderRoot]⟩,by simp [fourLeaf]⟩
  | .inr (.inr (.inr (.inr (.inl i)))) => .inl ⟨e-1-i.val,by omega⟩
  | .inr (.inr (.inr (.inr (.inr i)))) => .inl ⟨e+i.val+1,by omega⟩

theorem regularSixVertex_left (a b c d e f : ℕ) :
    Function.LeftInverse (regularSixBack a b c d e f) (regularSixVertex a b c d e f) := by
  intro x
  rcases x with i | ⟨x,hx⟩
  · simp only [regularSixVertex]
    split_ifs <;> simp [regularSixBack,pathJunction,Fin.ext_iff] <;> omega
  · rcases x with j | ⟨x,hx'⟩
    · have hj : j.val≠d := by intro he; exact hx (congrArg Sum.inl (Fin.ext he))
      simp [regularSixVertex,regularSixBack,hj]
    · rcases x with j | j
      · have hj : j.val≠a := by intro he; exact hx' (congrArg Sum.inl (Fin.ext he))
        simp only [regularSixVertex]
        split_ifs <;> simp [regularSixBack,Subtype.ext_iff,Fin.ext_iff] <;> omega
      · rfl

theorem regularSixVertex_bijective (a b c d e f : ℕ) :
    Function.Bijective (regularSixVertex a b c d e f) := by
  apply bijective_of_injective_equal_card _ (regularSixVertex_left a b c d e f).injective
  simp [RegularV,FourV,SpiderV,SixV,ArmsV,Fintype.card_subtype_compl,Fintype.card_subtype_eq]
  omega

def regularSixEdge (a b c d e f : ℕ) : RegularE a b c d e f → SixE a b (c+1) d e f
  | .inl i => if h : i.val<e then .inr (.inr (.inr (.inr (.inl ⟨e-1-i.val,by omega⟩))))
      else .inr (.inr (.inr (.inr (.inr ⟨i.val-e,by omega⟩))))
  | .inr (.inl i) => .inl i
  | .inr (.inr (.inl i)) => if h : i.val<a then .inr (.inl ⟨a-1-i.val,by omega⟩)
      else .inr (.inr (.inl ⟨i.val-a,by omega⟩))
  | .inr (.inr (.inr none)) => .inr (.inr (.inr (.inl 0)))
  | .inr (.inr (.inr (some i))) => .inr (.inr (.inr (.inl ⟨i.val+1,by omega⟩)))

def regularSixEdgeBack (a b c d e f : ℕ) : SixE a b (c+1) d e f → RegularE a b c d e f
  | .inl i => .inr (.inl i)
  | .inr (.inl i) => .inr (.inr (.inl ⟨a-1-i.val,by omega⟩))
  | .inr (.inr (.inl i)) => .inr (.inr (.inl ⟨a+i.val,by omega⟩))
  | .inr (.inr (.inr (.inl i))) => if h : i.val=0 then .inr (.inr (.inr none))
      else .inr (.inr (.inr (some ⟨i.val-1,by omega⟩)))
  | .inr (.inr (.inr (.inr (.inl i)))) => .inl ⟨e-1-i.val,by omega⟩
  | .inr (.inr (.inr (.inr (.inr i)))) => .inl ⟨e+i.val,by omega⟩

theorem regularSixEdge_left (a b c d e f : ℕ) :
    Function.LeftInverse (regularSixEdgeBack a b c d e f) (regularSixEdge a b c d e f) := by
  intro x
  rcases x with i | i
  · simp only [regularSixEdge]; split_ifs <;> simp [regularSixEdgeBack,Fin.ext_iff] <;> omega
  · rcases i with i | i
    · rfl
    · rcases i with i | i
      · simp only [regularSixEdge]; split_ifs <;> simp [regularSixEdgeBack,Fin.ext_iff] <;> omega
      · cases i <;> simp [regularSixEdge,regularSixEdgeBack,Fin.ext_iff]

theorem regularSixEdge_bijective (a b c d e f : ℕ) :
    Function.Bijective (regularSixEdge a b c d e f) := by
  apply bijective_of_injective_equal_card _ (regularSixEdge_left a b c d e f).injective
  simp [RegularE,FourE,SpiderE,SixE,ArmsV]
  omega

theorem regularSix_endpoints (a b c d e f : ℕ) (hd : 1≤d) (i : RegularE a b c d e f) :
    (regularSixVertex a b c d e f (regularEnds a b c d e f i).1,
      regularSixVertex a b c d e f (regularEnds a b c d e f i).2)=
      sixEnds a b (c+1) d e f (regularSixEdge a b c d e f i) ∨
    (regularSixVertex a b c d e f (regularEnds a b c d e f i).1,
      regularSixVertex a b c d e f (regularEnds a b c d e f i).2)=
      (sixEnds a b (c+1) d e f (regularSixEdge a b c d e f i)).swap := by
  rcases i with i | i
  · by_cases hi : i.val<e
    · right
      by_cases hb : i.val+1=e
      · simp [regularEnds,wedgeEnds,pathEnds,regularSixVertex,regularSixEdge,sixEnds,armEnds,
          hi,hb,show i.val≠e by omega,show ¬i.val+1<e by omega,
          show e-1-i.val=0 by omega,Prod.ext_iff,Fin.ext_iff]
      · simp [regularEnds,wedgeEnds,pathEnds,regularSixVertex,regularSixEdge,sixEnds,armEnds,
          hi,hb,show i.val+1<e by omega,show e-1-i.val≠0 by omega,Prod.ext_iff,Fin.ext_iff]
        omega
    · left
      by_cases hb : i.val=e
      · simp [regularEnds,wedgeEnds,pathEnds,regularSixVertex,regularSixEdge,sixEnds,armEnds,
          hi,hb,show ¬i.val+1<e by omega,Prod.ext_iff,Fin.ext_iff]
      · simp [regularEnds,wedgeEnds,pathEnds,regularSixVertex,regularSixEdge,sixEnds,armEnds,
          hi,hb,show ¬i.val+1<e by omega,show i.val+1≠e by omega,
          show i.val-e≠0 by omega,Prod.ext_iff,Fin.ext_iff]
        omega
  · rcases i with i | i
    · left
      by_cases hb : i.val+1=d
      · simp [regularEnds,wedgeEnds,fourEnds,pathEnds,wedgeVertex,fourLeaf,regularSixVertex,
          regularSixEdge,sixEnds,pathJunction,hb,show i.val≠d by omega,Prod.ext_iff,Fin.ext_iff]
      · simp [regularEnds,wedgeEnds,fourEnds,pathEnds,wedgeVertex,fourLeaf,regularSixVertex,
          regularSixEdge,sixEnds,pathJunction,hb,show i.val≠d by omega,Prod.ext_iff,Fin.ext_iff]
    · rcases i with i | i
      · by_cases hi : i.val<a
        · right
          by_cases hb : i.val+1=a
          · simp [regularEnds,wedgeEnds,fourEnds,spiderEnds,Math15.Labeling.joinEnds,
              pathEnds,wedgeVertex,fourLeaf,spiderRoot,pathJunction,regularSixVertex,
              regularSixEdge,sixEnds,armEnds,hi,hb,show i.val≠a by omega,
              show 0≠d by omega,show a-1-i.val=0 by omega,Prod.ext_iff,Fin.ext_iff]
          · simp [regularEnds,wedgeEnds,fourEnds,spiderEnds,Math15.Labeling.joinEnds,
              pathEnds,wedgeVertex,fourLeaf,spiderRoot,pathJunction,regularSixVertex,
              regularSixEdge,sixEnds,armEnds,hi,hb,show i.val≠a by omega,
              show i.val+1<a by omega,show a-1-i.val≠0 by omega,Prod.ext_iff,Fin.ext_iff]
            omega
        · left
          by_cases hb : i.val=a
          · simp [regularEnds,wedgeEnds,fourEnds,spiderEnds,Math15.Labeling.joinEnds,
              pathEnds,wedgeVertex,fourLeaf,spiderRoot,pathJunction,regularSixVertex,
              regularSixEdge,sixEnds,armEnds,hi,hb,show 0≠d by omega,Prod.ext_iff,Fin.ext_iff]
          · simp [regularEnds,wedgeEnds,fourEnds,spiderEnds,Math15.Labeling.joinEnds,
              pathEnds,wedgeVertex,fourLeaf,spiderRoot,pathJunction,regularSixVertex,
              regularSixEdge,sixEnds,armEnds,hi,hb,show i.val+1≠a by omega,
              show ¬i.val+1<a by omega,show i.val-a≠0 by omega,Prod.ext_iff,Fin.ext_iff]
            omega
      · left
        cases i with
        | none =>
          simp [regularEnds,wedgeEnds,fourEnds,spiderEnds,Math15.Labeling.joinEnds,
            pathEnds,wedgeVertex,fourLeaf,spiderRoot,pathJunction,regularSixVertex,
            regularSixEdge,sixEnds,armEnds,show 0≠d by omega,Prod.ext_iff,Fin.ext_iff]
        | some i =>
          simp [regularEnds,wedgeEnds,fourEnds,spiderEnds,Math15.Labeling.joinEnds,
            pathEnds,wedgeVertex,fourLeaf,spiderRoot,pathJunction,regularSixVertex,
            regularSixEdge,sixEnds,armEnds,Prod.ext_iff,Fin.ext_iff]

end Math15Source10
#print axioms Math15Source10.regularSixVertex_bijective
#print axioms Math15Source10.regularSixEdge_bijective
