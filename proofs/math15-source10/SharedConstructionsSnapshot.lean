import Mathlib.Tactic
import Mathlib.Data.Nat.Dist

/- Generic certificates use an explicit type of edges. Every edge occurs once;
   this avoids silently forgetting multiplicities when constructions are glued. -/
namespace Math15.Labeling

def Good {V E : Type*} (m : ℕ) (f : V → ℕ) (ends : E → V × V) : Prop :=
  Function.Injective f ∧ (∀ v, f v ≤ m) ∧
  (∀ e, 0 < Nat.dist (f (ends e).1) (f (ends e).2)) ∧
  ∀ d, 1 ≤ d → d ≤ m → ∃! e, Nat.dist (f (ends e).1) (f (ends e).2) = d

theorem reflect_dist {m a b : ℕ} (ha : a ≤ m) (hb : b ≤ m) :
    Nat.dist (m-a) (m-b) = Nat.dist a b := by
  simp only [Nat.dist]
  omega

def leafLabel {V : Type*} (m : ℕ) (f : V → ℕ) : Option V → ℕ
  | none => 0
  | some v => m+1-f v

def leafEnds {V E : Type*} (r : V) (ends : E → V × V) :
    Option E → Option V × Option V
  | none => (none, some r)
  | some e => (some (ends e).1, some (ends e).2)

theorem leaf_old_dist {V E : Type*} {m : ℕ} {f : V → ℕ}
    {ends : E → V × V} (hb : ∀ v, f v ≤ m) (r : V) (e : E) :
    Nat.dist (leafLabel m f (leafEnds r ends (some e)).1)
      (leafLabel m f (leafEnds r ends (some e)).2) =
      Nat.dist (f (ends e).1) (f (ends e).2) := by
  exact reflect_dist (by have := hb (ends e).1; omega)
    (by have := hb (ends e).2; omega)

theorem leaf_new_dist {V E : Type*} {m : ℕ} {f : V → ℕ}
    {ends : E → V × V} {r : V} (hr : f r = 0) :
    Nat.dist (leafLabel m f (leafEnds r ends none).1)
      (leafLabel m f (leafEnds r ends none).2) = m+1 := by
  simp [leafLabel, leafEnds, hr, Nat.dist]

/-- Adding a new leaf at a zero-labeled root yields a labeling in which the
    new leaf receives zero. The root changes to the new leaf. -/
theorem add_leaf {V E : Type*} {m : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Good m f ends) (r : V) (hr : f r = 0) :
    Good (m+1) (leafLabel m f) (leafEnds r ends) := by
  rcases h with ⟨hi, hb, hp, hu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v huv
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some v =>
        have := hb v
        simp only [leafLabel] at huv
        omega
    | some u =>
      cases v with
      | none =>
        have := hb u
        simp only [leafLabel] at huv
        omega
      | some v =>
        congr 1
        apply hi
        have := hb u
        have := hb v
        simp only [leafLabel] at huv
        omega
  · intro v
    cases v <;> simp [leafLabel]
  · intro e
    cases e with
    | none => rw [leaf_new_dist hr]; omega
    | some e => rw [leaf_old_dist hb r e]; exact hp e
  · intro d hd hdm
    by_cases hm : d = m+1
    · subst d
      refine ⟨none, leaf_new_dist hr, ?_⟩
      intro e he
      cases e with
      | none => rfl
      | some e =>
        rw [leaf_old_dist hb r e] at he
        have h1 := hb (ends e).1
        have h2 := hb (ends e).2
        simp only [Nat.dist] at he
        omega
    · have hdm' : d ≤ m := by omega
      obtain ⟨e, he, heuniq⟩ := hu d hd hdm'
      refine ⟨some e, ?_, ?_⟩
      · exact (leaf_old_dist hb r e).trans he
      · intro e' he'
        cases e' with
        | none => rw [leaf_new_dist hr] at he'; omega
        | some e' =>
          rw [leaf_old_dist hb r e'] at he'
          exact congrArg some (heuniq e' he')

theorem add_leaf_root {V : Type*} (m : ℕ) (f : V → ℕ) :
    leafLabel m f none = 0 := rfl

def Alpha {V E : Type*} (k : ℕ) (f : V → ℕ) (ends : E → V × V) : Prop :=
  ∀ e, (f (ends e).1 ≤ k ∧ k < f (ends e).2) ∨
    (f (ends e).2 ≤ k ∧ k < f (ends e).1)

def gap (k r x : ℕ) : ℕ := if x ≤ k then x else x+r

theorem gap_dist {k r a b : ℕ}
    (h : (a ≤ k ∧ k < b) ∨ (b ≤ k ∧ k < a)) :
    Nat.dist (gap k r a) (gap k r b) = Nat.dist a b+r := by
  rcases h with h | h
  · simp only [gap, if_pos h.1, if_neg (by omega : ¬ b ≤ k), Nat.dist]
    omega
  · simp only [gap, if_pos h.1, if_neg (by omega : ¬ a ≤ k), Nat.dist]
    omega

def joinLabel {V W : Type*} (k r : ℕ) (f : V → ℕ) (g : W → ℕ) : V ⊕ W → ℕ
  | Sum.inl v => gap k r (f v)
  | Sum.inr w => g w+k+1

def joinEnds {V W E F : Type*} (u : V) (v : W)
    (a : E → V × V) (b : F → W × W) : E ⊕ Option F → (V ⊕ W) × (V ⊕ W)
  | Sum.inl e => (Sum.inl (a e).1, Sum.inl (a e).2)
  | Sum.inr none => (Sum.inl u, Sum.inr v)
  | Sum.inr (some e) => (Sum.inr (b e).1, Sum.inr (b e).2)

theorem join_left_dist {V W E F : Type*} {k r : ℕ} {f : V → ℕ} {g : W → ℕ}
    {a : E → V × V} {b : F → W × W} (ha : Alpha k f a) (u : V) (v : W) (e : E) :
    Nat.dist (joinLabel k r f g (joinEnds u v a b (Sum.inl e)).1)
      (joinLabel k r f g (joinEnds u v a b (Sum.inl e)).2) =
      Nat.dist (f (a e).1) (f (a e).2)+r := by
  exact gap_dist (ha e)

theorem join_right_dist {V W E F : Type*} (k r : ℕ) (f : V → ℕ) (g : W → ℕ)
    (a : E → V × V) (b : F → W × W) (u : V) (v : W) (e : F) :
    Nat.dist (joinLabel k r f g (joinEnds u v a b (Sum.inr (some e))).1)
      (joinLabel k r f g (joinEnds u v a b (Sum.inr (some e))).2) =
      Nat.dist (g (b e).1) (g (b e).2) := by
  simp only [joinLabel, joinEnds, Nat.dist]
  omega

theorem join_bridge_dist {V W E F : Type*} {k m : ℕ} {f : V → ℕ} {g : W → ℕ}
    (a : E → V × V) (b : F → W × W) (u : V) (v : W)
    (hk : k ≤ m) (hu : f u = 0) (hv : g v = m-k) :
    Nat.dist (joinLabel k (m+1) f g (joinEnds u v a b (Sum.inr none)).1)
      (joinLabel k (m+1) f g (joinEnds u v a b (Sum.inr none)).2) = m+1 := by
  simp only [joinLabel, joinEnds, gap, hu, hv, Nat.zero_le, if_true, Nat.dist]
  omega

theorem good_dist_le {V E : Type*} {m : ℕ} {f : V → ℕ} {a : E → V × V}
    (h : Good m f a) (e : E) : Nat.dist (f (a e).1) (f (a e).2) ≤ m := by
  have := h.2.1 (a e).1
  have := h.2.1 (a e).2
  simp only [Nat.dist]
  omega

theorem join_matching_bridge_dist {V W E F : Type*} {k m : ℕ}
    {f : V → ℕ} {g : W → ℕ}
    (a : E → V × V) (b : F → W × W) (u : V) (v : W)
    (hmatch : (f u ≤ k ∧ g v+k = f u+m) ∨
      (k < f u ∧ f u = g v+k+1)) :
    Nat.dist (joinLabel k (m+1) f g (joinEnds u v a b (Sum.inr none)).1)
      (joinLabel k (m+1) f g (joinEnds u v a b (Sum.inr none)).2) = m+1 := by
  rcases hmatch with h | h
  · simp only [joinLabel, joinEnds, gap, if_pos h.1, Nat.dist]
    omega
  · simp only [joinLabel, joinEnds, gap, if_neg (by omega : ¬ f u ≤ k), Nat.dist]
    omega

/-- The attachment can be anywhere in the left alpha component. The two
    alternatives state the exact same-labeling boundary-rank compatibility.
    Any zero label elsewhere in the left component is preserved. -/
theorem join_at_matching_boundary {V W E F : Type*} {n m k : ℕ}
    {f : V → ℕ} {g : W → ℕ} {a : E → V × V} {b : F → W × W}
    (hf : Good n f a) (hg : Good m g b) (ha : Alpha k f a)
    (hk : k ≤ n) (u : V) (v : W)
    (hmatch : (f u ≤ k ∧ g v+k = f u+m) ∨
      (k < f u ∧ f u = g v+k+1)) :
    Good (n+m+1) (joinLabel k (m+1) f g) (joinEnds u v a b) := by
  have hl := join_left_dist (g := g) (b := b) (r := m+1) ha u v
  have hr := join_right_dist k (m+1) f g a b u v
  have hc := join_matching_bridge_dist a b u v hmatch
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        apply hf.1
        simp only [joinLabel, gap] at hxy
        split_ifs at hxy <;> omega
      | inr y =>
        have hy := hg.2.1 y
        simp only [joinLabel, gap] at hxy
        split_ifs at hxy <;> omega
    | inr x =>
      cases y with
      | inl y =>
        have hx := hg.2.1 x
        simp only [joinLabel, gap] at hxy
        split_ifs at hxy <;> omega
      | inr y =>
        apply congrArg Sum.inr
        apply hg.1
        simp only [joinLabel] at hxy
        omega
  · intro x
    cases x with
    | inl x =>
      have hx := hf.2.1 x
      simp only [joinLabel, gap]
      split_ifs <;> omega
    | inr x =>
      have hx := hg.2.1 x
      simp only [joinLabel]
      omega
  · intro e
    cases e with
    | inl e => rw [hl]; omega
    | inr e =>
      cases e with
      | none => rw [hc]; omega
      | some e => rw [hr]; exact hg.2.2.1 e
  · intro d hd hdm
    by_cases hsmall : d ≤ m
    · obtain ⟨e, he, heuniq⟩ := hg.2.2.2 d hd hsmall
      refine ⟨Sum.inr (some e), ?_, ?_⟩
      · exact (hr e).trans he
      · intro e' he'
        cases e' with
        | inl e' => rw [hl] at he'; omega
        | inr e' =>
          cases e' with
          | none => rw [hc] at he'; omega
          | some e' =>
            rw [hr] at he'
            exact congrArg (fun z => Sum.inr (some z)) (heuniq e' he')
    · by_cases heq : d = m+1
      · subst d
        refine ⟨Sum.inr none, hc, ?_⟩
        intro e' he'
        cases e' with
        | inl e' =>
          have hpos := hf.2.2.1 e'
          rw [hl] at he'; omega
        | inr e' =>
          cases e' with
          | none => rfl
          | some e' =>
            have hle := good_dist_le hg e'
            rw [hr] at he'; omega
      · have hd' : 1 ≤ d-(m+1) := by omega
        have hn' : d-(m+1) ≤ n := by omega
        obtain ⟨e, he, heuniq⟩ := hf.2.2.2 (d-(m+1)) hd' hn'
        refine ⟨Sum.inl e, ?_, ?_⟩
        · exact (hl e).trans (by omega)
        · intro e' he'
          cases e' with
          | inl e' =>
            rw [hl] at he'
            apply congrArg Sum.inl
            apply heuniq
            omega
          | inr e' =>
            cases e' with
            | none => rw [hc] at he'; omega
            | some e' =>
              have hle := good_dist_le hg e'
              rw [hr] at he'; omega

/-- Root-zero special case of the general joining theorem. -/
theorem join_at_prescribed_label {V W E F : Type*} {n m k : ℕ}
    {f : V → ℕ} {g : W → ℕ} {a : E → V × V} {b : F → W × W}
    (hf : Good n f a) (hg : Good m g b) (ha : Alpha k f a)
    (hk : k ≤ n) (hkm : k ≤ m) (u : V) (v : W)
    (hu : f u = 0) (hv : g v = m-k) :
    Good (n+m+1) (joinLabel k (m+1) f g) (joinEnds u v a b) := by
  apply join_at_matching_boundary hf hg ha hk u v
  exact Or.inl ⟨by omega, by omega⟩

theorem join_preserves_zero {V W : Type*} {k m : ℕ} {f : V → ℕ} {g : W → ℕ}
    {u : V} (hu : f u = 0) : joinLabel k (m+1) f g (Sum.inl u) = 0 := by
  simp [joinLabel, gap, hu]

end Math15.Labeling

#print axioms Math15.Labeling.add_leaf
#print axioms Math15.Labeling.join_at_prescribed_label
#print axioms Math15.Labeling.join_at_matching_boundary
#print axioms Math15.Labeling.join_preserves_zero
