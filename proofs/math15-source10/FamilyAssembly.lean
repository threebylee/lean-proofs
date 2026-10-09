import GraphPresentation
import StemNearEnd
import StemNearLeaf
import Target10

namespace Math15Source10

/-- Concrete presentations for the exceptional labeling constructions.
This predicate specifies graph shapes and positive arm lengths; it assumes
no labeling. The full Source 10 proof uses the six-path construction in
CanonicalClosure rather than assuming this presentation for every tree. -/
inductive ExceptionalPresentation {n : ℕ} (G : SimpleGraph (Fin n)) : Prop
  | large (a b c s : ℕ) (ha : 3≤a) (hb : a≤b) (hc : b≤c+1)
      (e : ModelV a b c s ≃ Fin n) (hp : Presents G (modelEnds a b c s) e)
  | shortOne (a b s : ℕ) (ha : 1≤a) (hb : 1≤b) (hex : a≠2 ∨ b≠2)
      (e : ModelV a b 0 s ≃ Fin n) (hp : Presents G (modelEnds a b 0 s) e)
  | shortTwo (a b s : ℕ) (ha : 1≤a) (hb : 1≤b) (hex : a≠2 ∨ b≠2)
      (e : ModelV a b 1 s ≃ Fin n) (hp : Presents G (modelEnds a b 1 s) e)
  | allTwo (D : ℕ) (hD : 1≤D) (e : Bistar.PhysicalV D 3 2 ≃ Fin n)
      (hp : Presents G (Bistar.physicalEnds D 3 2) e)

theorem exceptional_presentation_graceful {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : ExceptionalPresentation G) : Math15.Graceful.IsGraceful G := by
  cases h with
  | large a b c s ha hb hc e hp =>
    obtain ⟨f,hf⟩ := model_large_all ha hb hc
    exact graceful_of_complete_presentation hf G e hp
  | shortOne a b s ha hb hex e hp =>
    obtain ⟨f,hf⟩ := model_short_one ha hb hex
    exact graceful_of_complete_presentation hf G e hp
  | shortTwo a b s ha hb hex e hp =>
    obtain ⟨f,hf⟩ := model_short_two ha hb hex
    exact graceful_of_complete_presentation hf G e hp
  | allTwo D hD e hp =>
    obtain ⟨f,hf,_⟩ := Bistar.physical_root_zero D 3 2 hD
    exact graceful_of_complete_presentation hf G e hp

/-- An optional structural premise for the conditional presentation theorem. -/
def Target12Decomposition : Prop := ∀ n (G : SimpleGraph (Fin n)),
  G.IsTree → (∃ u v, Math15.Graceful.Branch43 G u v ∧ Math15.Graceful.TwoLengthTwoArms G v) →
  ExceptionalPresentation G

/-- A conditional route from an exceptional presentation to Source 12.
The unconditional result is source12_verified in CanonicalClosure. -/
theorem target12_of_decomposition (hd : Target12Decomposition) : Math15.Graceful.Target12 := by
  intro n G ht hb
  exact exceptional_presentation_graceful (hd n G ht hb)

end Math15Source10
#print axioms Math15Source10.exceptional_presentation_graceful
#print axioms Math15Source10.target12_of_decomposition
