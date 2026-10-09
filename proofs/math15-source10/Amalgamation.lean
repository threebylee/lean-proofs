import AlphaJoin

namespace Math15Source10

def wedgeVertex {V W : Type*} [DecidableEq W] (u : V) (v : W) (w : W) : V ⊕ {w : W // w≠v} :=
  if h : w=v then .inl u else .inr ⟨w,h⟩

def wedgeEnds {V W E F : Type*} [DecidableEq W] (u : V) (v : W)
    (a : E → V × V) (b : F → W × W) : E ⊕ F →
      (V ⊕ {w : W // w≠v}) × (V ⊕ {w : W // w≠v})
  | .inl e => (.inl (a e).1,.inl (a e).2)
  | .inr e => (wedgeVertex u v (b e).1,wedgeVertex u v (b e).2)

def wedgeLabel {V W : Type*} {v : W} (k m : ℕ) (f : V → ℕ) (g : W → ℕ) :
    V ⊕ {w : W // w≠v} → ℕ
  | .inl x => Math15.Labeling.gap k m (f x)
  | .inr x => g x.val+k

theorem wedge_right_label {V W : Type*} [DecidableEq W] {k m : ℕ}
    {f : V → ℕ} {g : W → ℕ} (u : V) (v : W) (hu : f u=k) (hv : g v=0) (w : W) :
    wedgeLabel k m f g (wedgeVertex u v w)=g w+k := by
  by_cases hw : w=v
  · subst w; simp [wedgeVertex,wedgeLabel,Math15.Labeling.gap,hu,hv]
  · simp [wedgeVertex,wedgeLabel,hw]

/-- Identify a boundary-labeled alpha vertex with a zero-labeled graceful
vertex. The shared vertex occurs once, so every label and edge is accounted for. -/
theorem wedge_complete {V W E F : Type*} [DecidableEq W] {n m k : ℕ}
    {f : V → ℕ} {g : W → ℕ} {a : E → V × V} {b : F → W × W}
    (hf : Complete n f a) (hg : Complete m g b) (ha : Alpha k f a)
    (hk : k≤n) (u : V) (v : W) (hu : f u=k) (hv : g v=0) :
    Complete (n+m) (wedgeLabel k m f g) (wedgeEnds u v a b) := by
  have hgp (w : {w : W // w≠v}) : 0<g w.val := by
    have hn : g w.val≠0 := fun h => w.property (hg.1 (h.trans hv.symm))
    omega
  have hl (e : E) :
      Nat.dist (wedgeLabel k m f g (wedgeEnds u v a b (.inl e)).1)
        (wedgeLabel k m f g (wedgeEnds u v a b (.inl e)).2)=
        Nat.dist (f (a e).1) (f (a e).2)+m := Math15.Labeling.gap_dist (ha e)
  have hr (e : F) :
      Nat.dist (wedgeLabel k m f g (wedgeEnds u v a b (.inr e)).1)
        (wedgeLabel k m f g (wedgeEnds u v a b (.inr e)).2)=
        Nat.dist (g (b e).1) (g (b e).2) := by
    simp only [wedgeEnds,wedge_right_label u v hu hv,Nat.dist]; omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl; apply hf.1
        simp only [wedgeLabel,Math15.Labeling.gap] at he
        split_ifs at he <;> omega
      | inr y =>
        have := hgp y; have := hg.2.1 y.val
        simp only [wedgeLabel,Math15.Labeling.gap] at he
        split_ifs at he <;> omega
    | inr x =>
      cases y with
      | inl y =>
        have := hgp x; have := hg.2.1 x.val
        simp only [wedgeLabel,Math15.Labeling.gap] at he
        split_ifs at he <;> omega
      | inr y =>
        apply congrArg Sum.inr; apply Subtype.ext; apply hg.1
        simp only [wedgeLabel] at he; omega
  · intro x
    cases x with
    | inl x =>
      have := hf.2.1 x
      simp only [wedgeLabel,Math15.Labeling.gap]; split_ifs <;> omega
    | inr x => have := hg.2.1 x.val; simp only [wedgeLabel]; omega
  · intro d hd
    by_cases hlo : d≤k
    · obtain ⟨x,hx⟩ := hf.2.2.1 d (by omega)
      exact ⟨.inl x,by simp [wedgeLabel,Math15.Labeling.gap,hx,hlo]⟩
    · by_cases hmid : d≤k+m
      · obtain ⟨x,hx⟩ := hg.2.2.1 (d-k) (by omega)
        have hn : x≠v := by intro he; subst x; rw [hv] at hx; omega
        refine ⟨.inr ⟨x,hn⟩,?_⟩
        simp only [wedgeLabel,hx]; omega
      · obtain ⟨x,hx⟩ := hf.2.2.1 (d-m) (by omega)
        refine ⟨.inl x,?_⟩
        simp only [wedgeLabel,Math15.Labeling.gap,hx]; split_ifs <;> omega
  · intro e
    cases e with
    | inl e => rw [hl]; have := hf.2.2.2.1 e; omega
    | inr e => rw [hr]; exact hg.2.2.2.1 e
  · intro d hd hdm
    by_cases hsmall : d≤m
    · obtain ⟨e,he,huq⟩ := hg.2.2.2.2 d hd hsmall
      refine ⟨.inr e,(hr e).trans he,?_⟩
      intro z hz
      cases z with
      | inl z => rw [hl] at hz; have := hf.2.2.2.1 z; omega
      | inr z => rw [hr] at hz; exact congrArg Sum.inr (huq z hz)
    · obtain ⟨e,he,huq⟩ := hf.2.2.2.2 (d-m) (by omega) (by omega)
      refine ⟨.inl e,by dsimp only; rw [hl,he]; omega,?_⟩
      intro z hz
      cases z with
      | inl z => rw [hl] at hz; exact congrArg Sum.inl (huq z (by omega))
      | inr z =>
        rw [hr] at hz
        have := hg.2.1 (b z).1; have := hg.2.1 (b z).2
        simp only [Nat.dist] at hz; omega

theorem wedge_zero_complete {V W E F : Type*} [DecidableEq W] {n m k : ℕ}
    {f : V → ℕ} {g : W → ℕ} {a : E → V × V} {b : F → W × W}
    (hf : Complete n f a) (hg : Complete m g b) (ha : Alpha k f a)
    (hk : k≤n) (u : V) (v : W) (hu : f u=0) (hv : g v=0) :
    ∃ F : V ⊕ {w : W // w≠v} → ℕ, Complete (n+m) F (wedgeEnds u v a b) := by
  exact ⟨_,wedge_complete (reverse_complete hf ha hk) hg
    (reverse_alpha hf.2.1 ha) hk u v (by simp [reverseLabel,hu]) hv⟩

end Math15Source10
#print axioms Math15Source10.wedge_complete
#print axioms Math15Source10.wedge_zero_complete
