import SpiderZero
import FamilyAssembly

namespace Math15Source10

abbrev SpiderV (a b c : ℕ) := Fin (a+b+1) ⊕ Fin (c+1)
abbrev SpiderE (a b c : ℕ) := Fin (a+b) ⊕ Option (Fin c)
def spiderRoot (a b c : ℕ) : SpiderV a b c := .inl (pathJunction a b)
abbrev FourV (a b c d : ℕ) := Fin (d+1) ⊕ {v : SpiderV a b c // v≠spiderRoot a b c}
abbrev FourE (a b c d : ℕ) := Fin d ⊕ SpiderE a b c
def fourEnds (a b c d : ℕ) : FourE a b c d → FourV a b c d × FourV a b c d :=
  wedgeEnds (0 : Fin (d+1)) (spiderRoot a b c) (pathEnds d) (spiderEnds a b c)
def fourLeaf (a b c d : ℕ) : FourV a b c d := .inl ⟨d,by omega⟩

/-- Four arms of lengths a,b,c+1,d, with label zero at the selected d-arm leaf. -/
theorem four_leaf_zero (a b c d : ℕ) (ha : 1≤a) (hb : a≤b) (hc : b≤c+1) :
    ∃ f : FourV a b c d → ℕ, Complete (d+(a+b+c+1)) f (fourEnds a b c d) ∧
      f (fourLeaf a b c d)=0 := by
  obtain ⟨f,hf,h0⟩ := spider_center_zero_all a b c ha hb hc
  exact rooted_leaf_extension hf (spiderRoot a b c) h0 d

abbrev RegularV (a b c d e f : ℕ) :=
  Fin (e+f+1) ⊕ {v : FourV a b c d // v≠fourLeaf a b c d}
abbrev RegularE (a b c d e f : ℕ) := Fin (e+f) ⊕ FourE a b c d
def regularEnds (a b c d e f : ℕ) : RegularE a b c d e f → RegularV a b c d e f × RegularV a b c d e f :=
  wedgeEnds (pathJunction e f) (fourLeaf a b c d) (pathEnds (e+f)) (fourEnds a b c d)

/-- Literal six-arm tree T(a,b,c+1;d;e,f), in an amalgamated presentation. -/
theorem regular_complete (a b c d e f : ℕ) (ha : 1≤a) (hb : a≤b) (hc : b≤c+1)
    (he : 1≤e) (hf : 1≤f) (hex : e≠2 ∨ f≠2) :
    ∃ F : RegularV a b c d e f → ℕ,
      Complete (e+f+(d+(a+b+c+1))) F (regularEnds a b c d e f) := by
  obtain ⟨g,hg,hg0⟩ := four_leaf_zero a b c d ha hb hc
  obtain ⟨k,h,hk,hh,hal,hh0⟩ := pathZero_all e f he hf hex
  exact wedge_zero_complete hh hg hal hk (pathJunction e f) (fourLeaf a b c d) hh0 hg0

/-- All six-arm shapes, with no labeling assumption. Arm ordering in each
constructor is purely a choice of presentation. -/
inductive Source10Presentation {n : ℕ} (G : SimpleGraph (Fin n)) : Prop
  | regular (a b c d e f : ℕ) (ha : 1≤a) (hb : a≤b) (hc : b≤c+1)
      (hd : 1≤d) (he : 1≤e) (hf : 1≤f) (hex : e≠2 ∨ f≠2)
      (equiv : RegularV a b c d e f ≃ Fin n) (hp : Presents G (regularEnds a b c d e f) equiv)
  | exceptional (h : ExceptionalPresentation G)

theorem source10_presentation_graceful {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : Source10Presentation G) : Math15.Graceful.IsGraceful G := by
  cases h with
  | regular a b c d e f ha hb hc hd he hf hex equiv hp =>
    obtain ⟨F,hF⟩ := regular_complete a b c d e f ha hb hc he hf hex
    exact graceful_of_complete_presentation hF G equiv hp
  | exceptional h => exact exceptional_presentation_graceful h

/-- The remaining canonical-target obligation is finite-tree structure only.
This is an unproved proposition, not an axiom or a completed target. -/
def Target10Decomposition : Prop := ∀ n (G : SimpleGraph (Fin n)),
  G.IsTree → (∃ u v, Math15.Graceful.Branch43 G u v) → Source10Presentation G

theorem target10_of_decomposition (hd : Target10Decomposition) : Math15.Graceful.Target10 := by
  intro n G ht hb
  exact source10_presentation_graceful (hd n G ht hb)

end Math15Source10
#print axioms Math15Source10.four_leaf_zero
#print axioms Math15Source10.regular_complete
#print axioms Math15Source10.source10_presentation_graceful
#print axioms Math15Source10.target10_of_decomposition
