import MatchingLift
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Math15.Graceful
open Finset

-- Literal definitions from the challenge's Math15/Graceful.lean.
noncomputable def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)).card

def IsGraceful {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → ℕ, Function.Injective f ∧
    (∀ v, f v ≤ edgeCount G) ∧
    (∀ d, 1 ≤ d → d ≤ edgeCount G →
      ∃! e : Fin n × Fin n, e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ Nat.dist (f e.1) (f e.2) = d)
end Math15.Graceful

namespace Math15Source10
open Finset

def sortedEnds {V E : Type*} {m : ℕ} (f : V → ℕ) (hb : ∀ v, f v ≤ m)
    (ends : E → V × V) (e : E) : Fin (m+1) × Fin (m+1) :=
  let a : Fin (m+1) := ⟨f (ends e).1, by have := hb (ends e).1; omega⟩
  let b : Fin (m+1) := ⟨f (ends e).2, by have := hb (ends e).2; omega⟩
  if a < b then (a,b) else (b,a)

theorem sortedEnds_dist {V E : Type*} {m : ℕ} (f : V → ℕ) (hb : ∀ v, f v ≤ m)
    (ends : E → V × V) (e : E) :
    Nat.dist (sortedEnds f hb ends e).1.val (sortedEnds f hb ends e).2.val =
      Nat.dist (f (ends e).1) (f (ends e).2) := by
  simp only [sortedEnds]
  split_ifs <;> simp [Nat.dist_comm]

theorem sortedEnds_lt {V E : Type*} {m : ℕ} (f : V → ℕ) (hb : ∀ v, f v ≤ m)
    (ends : E → V × V) (hp : ∀ e, 0 < Nat.dist (f (ends e).1) (f (ends e).2)) (e : E) :
    (sortedEnds f hb ends e).1 < (sortedEnds f hb ends e).2 := by
  simp only [sortedEnds]
  split_ifs with hh
  · exact hh
  · have hd := hp e
    change f (ends e).2 < f (ends e).1
    change ¬ f (ends e).1 < f (ends e).2 at hh
    simp only [Nat.dist] at hd
    omega

def certificateGraph {V E : Type*} {m : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) : SimpleGraph (Fin (m+1)) where
  Adj a b := ∃ e, (a,b) = sortedEnds f h.2.1 ends e ∨ (b,a) = sortedEnds f h.2.1 ends e
  symm := by
    intro a b hab
    obtain ⟨e,he⟩ := hab
    exact ⟨e,he.symm⟩
  loopless := by
    intro a haa
    obtain ⟨e,he⟩ := haa
    have hh := sortedEnds_lt f h.2.1 ends h.2.2.2.1 e
    rcases he with he | he <;> rw [← he] at hh <;> exact (lt_irrefl a) hh

theorem sortedEnds_injective {V E : Type*} {m : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) : Function.Injective (sortedEnds f h.2.1 ends) := by
  intro e g he
  have hd : Nat.dist (f (ends e).1) (f (ends e).2) =
      Nat.dist (f (ends g).1) (f (ends g).2) := by
    have hh := congrArg (fun p : Fin (m+1) × Fin (m+1) => Nat.dist p.1.val p.2.val) he
    simpa only [sortedEnds_dist] using hh
  have hp := h.2.2.2.1 e
  have hb1 := h.2.1 (ends e).1
  have hb2 := h.2.1 (ends e).2
  have hm : Nat.dist (f (ends e).1) (f (ends e).2) ≤ m := by
    simp only [Nat.dist]; omega
  obtain ⟨z,hz,hu⟩ := h.2.2.2.2 _ hp hm
  exact (hu e rfl).trans (hu g hd.symm).symm

theorem complete_edge_card {V E : Type*} [Fintype E] {m : ℕ}
    {f : V → ℕ} {ends : E → V × V} (h : Complete m f ends) : Fintype.card E = m := by
  let w : E → Fin m := fun e => ⟨Nat.dist (f (ends e).1) (f (ends e).2)-1, by
    have hp := h.2.2.2.1 e
    have hb1 := h.2.1 (ends e).1
    have hb2 := h.2.1 (ends e).2
    simp only [Nat.dist] at *
    omega⟩
  have hw : ∀ e, (w e).val+1 = Nat.dist (f (ends e).1) (f (ends e).2) := by
    intro e
    have := h.2.2.2.1 e
    dsimp [w]
    omega
  have hi : Function.Injective w := by
    intro e g he
    have hd := congrArg Fin.val he
    have hm := (w e).isLt
    obtain ⟨z,hz,hu⟩ := h.2.2.2.2 ((w e).val+1) (by omega) (by omega)
    exact (hu e (hw e).symm).trans (hu g (by dsimp only; rw [← hw g]; omega)).symm
  have hs : Function.Surjective w := by
    intro d
    obtain ⟨e,he,_⟩ := h.2.2.2.2 (d.val+1) (by omega) (by omega)
    refine ⟨e, Fin.ext ?_⟩
    have := hw e
    omega
  simpa using Fintype.card_congr (Equiv.ofBijective w ⟨hi,hs⟩)

theorem certificateGraph_edgeCount {V E : Type*} [Fintype E] {m : ℕ}
    {f : V → ℕ} {ends : E → V × V} (h : Complete m f ends) :
    Math15.Graceful.edgeCount (certificateGraph h) = m := by
  classical
  have heq : (univ.filter (fun p : Fin (m+1) × Fin (m+1) =>
      p.1 < p.2 ∧ (certificateGraph h).Adj p.1 p.2)) =
      univ.image (sortedEnds f h.2.1 ends) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨hlt,e,he | he⟩
      · exact ⟨e,he.symm⟩
      · have hh := sortedEnds_lt f h.2.1 ends h.2.2.2.1 e
        rw [← he] at hh
        exact False.elim ((not_lt_of_ge (le_of_lt hlt)) hh)
    · rintro ⟨e,rfl⟩
      exact ⟨sortedEnds_lt f h.2.1 ends h.2.2.2.1 e, e, Or.inl rfl⟩
  unfold Math15.Graceful.edgeCount
  rw [heq, card_image_of_injective _ (sortedEnds_injective h), card_univ]
  exact complete_edge_card h

theorem certificateGraph_graceful {V E : Type*} [Fintype E] {m : ℕ}
    {f : V → ℕ} {ends : E → V × V} (h : Complete m f ends) :
    Math15.Graceful.IsGraceful (certificateGraph h) := by
  refine ⟨Fin.val, Fin.val_injective, ?_, ?_⟩
  · intro v
    rw [certificateGraph_edgeCount h]
    omega
  · intro d hd hm
    rw [certificateGraph_edgeCount h] at hm
    obtain ⟨e,he,hu⟩ := h.2.2.2.2 d hd hm
    refine ⟨sortedEnds f h.2.1 ends e, ?_, ?_⟩
    · refine ⟨sortedEnds_lt f h.2.1 ends h.2.2.2.1 e, ⟨e,Or.inl rfl⟩, ?_⟩
      rw [sortedEnds_dist,he]
    · intro p hp
      obtain ⟨hlt,hpa,hpd⟩ := hp
      obtain ⟨g,hg | hg⟩ := hpa
      · change p = sortedEnds f h.2.1 ends g at hg
        have hgd : Nat.dist (f (ends g).1) (f (ends g).2) = d := by
          rw [hg,sortedEnds_dist] at hpd
          exact hpd
        rw [hg,hu g hgd]
      · have hgl := sortedEnds_lt f h.2.1 ends h.2.2.2.1 g
        rw [← hg] at hgl
        exact False.elim ((not_lt_of_ge (le_of_lt hlt)) hgl)

end Math15Source10

#print axioms Math15Source10.certificateGraph_graceful
