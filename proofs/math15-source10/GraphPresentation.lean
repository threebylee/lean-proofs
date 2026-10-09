import SharedGraphSnapshot
import DoubleSpider

namespace Math15Source10
open Finset

/-- Exact adjacency presentation; no graph-theoretic hypothesis is hidden here. -/
def Presents {V E : Type*} {n : ℕ} (G : SimpleGraph (Fin n))
    (ends : E → V × V) (e : V ≃ Fin n) : Prop :=
  ∀ u v, G.Adj u v ↔ ∃ i,
    (u,v)=(e (ends i).1,e (ends i).2) ∨
    (v,u)=(e (ends i).1,e (ends i).2)

theorem graphOfGood_adj_iff {n m : ℕ} {E : Type*} [Fintype E]
    {f : Fin n → ℕ} {ends : E → Fin n × Fin n}
    (h : Math15.Labeling.Good m f ends) (u v : Fin n) :
    (Math15.Labeling.graphOfGood h).Adj u v ↔
      ∃ i, (u,v)=ends i ∨ (v,u)=ends i := by
  classical
  change ((u,v)∈univ.image (fun i => Math15.Labeling.orient (ends i)) ∨
    (v,u)∈univ.image (fun i => Math15.Labeling.orient (ends i))) ↔ _
  constructor
  · rintro (hp | hp)
    · obtain ⟨i,_,hi⟩ := mem_image.mp hp
      by_cases ho : (ends i).1 < (ends i).2
      · exact ⟨i,Or.inl (by simpa [Math15.Labeling.orient,ho] using hi.symm)⟩
      · refine ⟨i,Or.inr ?_⟩
        have hh := congrArg Prod.swap hi.symm
        simpa [Math15.Labeling.orient,ho] using hh
    · obtain ⟨i,_,hi⟩ := mem_image.mp hp
      by_cases ho : (ends i).1 < (ends i).2
      · exact ⟨i,Or.inr (by simpa [Math15.Labeling.orient,ho] using hi.symm)⟩
      · refine ⟨i,Or.inl ?_⟩
        have hh := congrArg Prod.swap hi.symm
        simpa [Math15.Labeling.orient,ho] using hh
  · rintro ⟨i,hi | hi⟩
    · by_cases ho : (ends i).1 < (ends i).2
      · exact Or.inl (mem_image.mpr ⟨i,mem_univ _,by simpa [Math15.Labeling.orient,ho] using hi.symm⟩)
      · refine Or.inr (mem_image.mpr ⟨i,mem_univ _,?_⟩)
        have hh := congrArg Prod.swap hi.symm
        simpa [Math15.Labeling.orient,ho] using hh
    · by_cases ho : (ends i).1 < (ends i).2
      · exact Or.inr (mem_image.mpr ⟨i,mem_univ _,by simpa [Math15.Labeling.orient,ho] using hi.symm⟩)
      · refine Or.inl (mem_image.mpr ⟨i,mem_univ _,?_⟩)
        have hh := congrArg Prod.swap hi.symm
        simpa [Math15.Labeling.orient,ho] using hh

theorem graceful_of_complete_presentation {V E : Type*} [Fintype E]
    {n m : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (G : SimpleGraph (Fin n)) (e : V ≃ Fin n)
    (hp : Presents G ends e) : Math15.Graceful.IsGraceful G := by
  have hg := Math15.Labeling.good_reindex_vertices h.good e
  have he : G=Math15.Labeling.graphOfGood hg := by
    ext u v
    exact (hp u v).trans (graphOfGood_adj_iff hg u v).symm
  rw [he]
  exact Math15.Labeling.graphOfGood_isGraceful hg (complete_edge_card h)

theorem model44_presented_graceful {n c s : ℕ} (hc : 3≤c)
    (G : SimpleGraph (Fin n)) (e : ModelV 4 4 c s ≃ Fin n)
    (hp : Presents G (modelEnds 4 4 c s) e) : Math15.Graceful.IsGraceful G := by
  obtain ⟨f,hf⟩ := model44_all c s hc
  exact graceful_of_complete_presentation hf G e hp

theorem model_one_presented_graceful {n a b c s : ℕ}
    (ha : 3≤a) (hb : a≤b) (hc : b≤c+1) (hex : a≠4 ∨ b≠4) (hs : s≠2)
    (G : SimpleGraph (Fin n)) (e : ModelV a b c s ≃ Fin n)
    (hp : Presents G (modelEnds a b c s) e) : Math15.Graceful.IsGraceful G := by
  obtain ⟨f,hf⟩ := model_one ha hb hc hex hs
  exact graceful_of_complete_presentation hf G e hp

end Math15Source10
#print axioms Math15Source10.graceful_of_complete_presentation
#print axioms Math15Source10.model44_presented_graceful
#print axioms Math15Source10.model_one_presented_graceful
