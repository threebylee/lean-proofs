-- Graph realization of complete edge-difference certificates.

import CanonicalBridge
import SharedConstructionsSnapshot

namespace Math15.Labeling
open Finset

def orient {n : ℕ} (p : Fin n × Fin n) : Fin n × Fin n :=
  if p.1 < p.2 then p else p.swap

theorem orient_lt {n : ℕ} {p : Fin n × Fin n} (h : p.1 ≠ p.2) :
    (orient p).1 < (orient p).2 := by
  simp only [orient]
  split_ifs with hp
  · exact hp
  · simp only [Prod.fst_swap, Prod.snd_swap]
    exact lt_of_le_of_ne (le_of_not_gt hp) (Ne.symm h)

theorem orient_dist {n : ℕ} (f : Fin n → ℕ) (p : Fin n × Fin n) :
    Nat.dist (f (orient p).1) (f (orient p).2) = Nat.dist (f p.1) (f p.2) := by
  simp only [orient]
  split_ifs <;> simp [Nat.dist_comm]

theorem good_edge_injective {V E : Type*} {m : ℕ} {f : V → ℕ}
    {ends : E → V × V} (h : Good m f ends) :
    Function.Injective (fun e => Nat.dist (f (ends e).1) (f (ends e).2)) := by
  intro e e' he
  obtain ⟨e₀, _, hu⟩ := h.2.2.2 _ (h.2.2.1 e) (good_dist_le h e)
  exact (hu e rfl).trans (hu e' he.symm).symm

theorem good_orient_injective {n m : ℕ} {E : Type*} {f : Fin n → ℕ}
    {ends : E → Fin n × Fin n} (h : Good m f ends) :
    Function.Injective (fun e => orient (ends e)) := by
  intro e e' he
  dsimp only at he
  apply good_edge_injective h
  change Nat.dist (f (ends e).1) (f (ends e).2) = Nat.dist (f (ends e').1) (f (ends e').2)
  rw [← orient_dist f (ends e), ← orient_dist f (ends e'), he]

noncomputable def edgePairs {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n × Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact univ.image (fun e => orient (ends e))

theorem edgePairs_lt {n m : ℕ} {E : Type*} [Fintype E]
    {f : Fin n → ℕ} {ends : E → Fin n × Fin n} (h : Good m f ends)
    {p : Fin n × Fin n} (hp : p ∈ edgePairs ends) : p.1 < p.2 := by
  classical
  obtain ⟨e, _, rfl⟩ := mem_image.mp hp
  apply orient_lt
  intro he
  have hh := h.2.2.1 e
  rw [he, Nat.dist_self] at hh
  omega

noncomputable def graphOfGood {n m : ℕ} {E : Type*} [Fintype E]
    {f : Fin n → ℕ} {ends : E → Fin n × Fin n} (h : Good m f ends) :
    SimpleGraph (Fin n) where
  Adj u v := (u,v) ∈ edgePairs ends ∨ (v,u) ∈ edgePairs ends
  symm := by intro u v huv; exact huv.symm
  loopless := by
    intro u hu
    rcases hu with hu | hu <;> have := edgePairs_lt h hu <;> exact (lt_irrefl u) this

theorem graphOfGood_count {n m : ℕ} {E : Type*} [Fintype E]
    {f : Fin n → ℕ} {ends : E → Fin n × Fin n} (h : Good m f ends) :
    Graceful.edgeCount (graphOfGood h) = Fintype.card E := by
  classical
  have hset : (univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (graphOfGood h).Adj p.1 p.2)) = edgePairs ends := by
    ext p
    simp only [mem_filter, mem_univ, true_and, graphOfGood]
    constructor
    · rintro ⟨hlt, hp | hp⟩
      · exact hp
      · have := edgePairs_lt h hp
        exact False.elim (lt_asymm hlt this)
    · intro hp
      exact ⟨edgePairs_lt h hp, Or.inl hp⟩
  change (univ.filter _).card = _
  rw [hset]
  unfold edgePairs
  rw [card_image_of_injective _ (good_orient_injective h), card_univ]

theorem graphOfGood_isGraceful {n m : ℕ} {E : Type*} [Fintype E]
    {f : Fin n → ℕ} {ends : E → Fin n × Fin n} (h : Good m f ends)
    (hcard : Fintype.card E = m) : Graceful.IsGraceful (graphOfGood h) := by
  classical
  have hm : Graceful.edgeCount (graphOfGood h) = m := (graphOfGood_count h).trans hcard
  refine ⟨f, h.1, ?_, ?_⟩
  · simpa only [hm] using h.2.1
  · intro d hd hdm
    rw [hm] at hdm
    obtain ⟨e, he, hu⟩ := h.2.2.2 d hd hdm
    have hp : orient (ends e) ∈ edgePairs ends := mem_image.mpr ⟨e, mem_univ _, rfl⟩
    refine ⟨orient (ends e), ⟨edgePairs_lt h hp, Or.inl hp, ?_⟩, ?_⟩
    · exact (orient_dist f (ends e)).trans he
    · intro p hpd
      have hpin : p ∈ edgePairs ends := by
        rcases hpd.2.1 with hp' | hp'
        · exact hp'
        · have := edgePairs_lt h hp'
          exact False.elim (lt_asymm hpd.1 this)
      obtain ⟨e', _, he'⟩ := mem_image.mp hpin
      have hdist : Nat.dist (f (ends e').1) (f (ends e').2) = d := by
        rw [← orient_dist f (ends e'), he']
        exact hpd.2.2
      rw [hu e' hdist] at he'
      exact he'.symm

theorem good_reindex_vertices {V W E : Type*} {m : ℕ} {f : V → ℕ}
    {ends : E → V × V} (h : Good m f ends) (e : V ≃ W) :
    Good m (fun w => f (e.symm w))
      (fun i => (e (ends i).1, e (ends i).2)) := by
  refine ⟨h.1.comp e.symm.injective, ?_, ?_, ?_⟩
  · intro w; exact h.2.1 _
  · simpa using h.2.2.1
  · simpa using h.2.2.2

end Math15.Labeling

#print axioms Math15.Labeling.graphOfGood_isGraceful
#print axioms Math15.Labeling.good_reindex_vertices
