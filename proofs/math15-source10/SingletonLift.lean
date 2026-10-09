import MatchingLift

namespace Math15Source10

abbrev ThinV {V : Type*} (r : V) := {p : V × Bool // p.2 = false ∨ p.1 ≠ r}

def thinLabel {V : Type*} {r : V} (m : ℕ) (f : V → ℕ) (p : ThinV r) : ℕ :=
  if p.val.2 then 2*m-1-2*f p.val.1 else 2*f p.val.1

def thinPort {V : Type*} {r : V} (v : V) (b : Bool) (h : v = r → b = false) : ThinV r :=
  ⟨(v,b), by by_cases hv : v = r; exact Or.inl (h hv); exact Or.inr hv⟩

def thinEnds {V E : Type*} {r : V} (ends : E → V × V) (side : E → Bool)
    (hr : ∀ e, (ends e).1 = r ∨ (ends e).2 = r → side e = false) :
    {v : V // v ≠ r} ⊕ E → ThinV r × ThinV r
  | .inl v => (⟨(v.val,false),Or.inl rfl⟩,⟨(v.val,true),Or.inr v.property⟩)
  | .inr e => (thinPort (ends e).1 (side e) (fun h => hr e (Or.inl h)),
      thinPort (ends e).2 (side e) (fun h => hr e (Or.inr h)))

theorem thin_small {V : Type*} {m : ℕ} {f : V → ℕ} {r : V}
    (hi : Function.Injective f) (hb : ∀ v, f v ≤ m) (hr : f r = m)
    (v : V) (hv : v ≠ r) : f v ≤ m-1 := by
  have := hb v
  have hn : f v ≠ m := fun h => hv (hi (h.trans hr.symm))
  omega

theorem thin_matching {V E : Type*} {r : V} (m : ℕ) (f : V → ℕ)
    (ends : E → V × V) (side : E → Bool) (hr) (v : {v : V // v ≠ r}) :
    Nat.dist (thinLabel m f (thinEnds ends side hr (.inl v)).1)
      (thinLabel m f (thinEnds ends side hr (.inl v)).2) =
      Nat.dist (2*f v.val) (2*m-1-2*f v.val) := by simp [thinEnds,thinLabel]

theorem thin_cross {V E : Type*} {m : ℕ} {f : V → ℕ} {r : V}
    (hi : Function.Injective f) (hb : ∀ v, f v ≤ m) (hroot : f r = m)
    (ends : E → V × V) (side : E → Bool)
    (hr : ∀ e, (ends e).1 = r ∨ (ends e).2 = r → side e = false) (e : E) :
    Nat.dist (thinLabel m f (thinEnds ends side hr (.inr e)).1)
      (thinLabel m f (thinEnds ends side hr (.inr e)).2) =
      2 * Nat.dist (f (ends e).1) (f (ends e).2) := by
  cases hs : side e with
  | false => simp [thinEnds,thinLabel,thinPort,hs,Nat.dist]; omega
  | true =>
    have hn1 : (ends e).1 ≠ r := by intro h; have := hr e (Or.inl h); simp_all
    have hn2 : (ends e).2 ≠ r := by intro h; have := hr e (Or.inr h); simp_all
    have h1 := thin_small hi hb hroot _ hn1
    have h2 := thin_small hi hb hroot _ hn2
    simp [thinEnds,thinLabel,thinPort,hs,Nat.dist]
    omega

/-- A near-perfect matching lift, leaving the maximally labeled vertex unpaired.
Every edge at that vertex uses the even side. -/
theorem singleton_lift {V E : Type*} {m : ℕ} {f : V → ℕ} {ends : E → V × V}
    (h : Complete m f ends) (hm : 1 ≤ m) (r : V) (hroot : f r = m)
    (side : E → Bool) (hr : ∀ e, (ends e).1 = r ∨ (ends e).2 = r → side e = false) :
    Complete (2*m) (thinLabel (r:=r) m f) (thinEnds ends side hr) := by
  rcases h with ⟨hi,hb,hs,hp,hu⟩
  have hsml := thin_small hi hb hroot
  have hpred : 2*(m-1)+1 = 2*m-1 := by omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro p q he
    obtain ⟨⟨v,b⟩,hv⟩ := p
    obtain ⟨⟨w,c⟩,hw⟩ := q
    apply Subtype.ext
    cases b <;> cases c <;> simp only [thinLabel,Bool.false_eq_true,↓reduceIte] at he
    · have : v = w := hi (by omega)
      subst w
      rfl
    · have hw' : w ≠ r := by simpa using hw
      have := hsml w hw'
      omega
    · have hv' : v ≠ r := by simpa using hv
      have := hsml v hv'
      omega
    · have hv' : v ≠ r := by simpa using hv
      have hw' : w ≠ r := by simpa using hw
      have := hsml v hv'
      have := hsml w hw'
      have : v = w := hi (by omega)
      subst w
      rfl
  · rintro ⟨⟨v,b⟩,hv⟩
    have := hb v
    cases b <;> simp [thinLabel] <;> omega
  · intro k hk
    by_cases he : k % 2 = 0
    · obtain ⟨v,hv⟩ := hs (k/2) (by omega)
      refine ⟨⟨(v,false),Or.inl rfl⟩,?_⟩
      simp [thinLabel,hv]
      omega
    · obtain ⟨v,hv⟩ := hs ((2*m-1-k)/2) (by omega)
      have hn : v ≠ r := by intro hv'; subst v; rw [hroot] at hv; omega
      refine ⟨⟨(v,true),Or.inr hn⟩,?_⟩
      simp [thinLabel,hv]
      omega
  · intro e
    cases e with
    | inl v =>
      rw [thin_matching,←hpred]
      have := matching_odd (hsml v.val v.property)
      omega
    | inr e =>
      rw [thin_cross hi hb hroot]
      have := hp e
      omega
  · intro d hd hdm
    by_cases he : d % 2 = 0
    · obtain ⟨e,heq,heuniq⟩ := hu (d/2) (by omega) (by omega)
      refine ⟨.inr e,?_,?_⟩
      · dsimp only
        rw [thin_cross hi hb hroot,heq]
        omega
      · intro z hz
        cases z with
        | inl v =>
          rw [thin_matching,←hpred] at hz
          have := matching_odd (hsml v.val v.property)
          omega
        | inr z =>
          rw [thin_cross hi hb hroot] at hz
          exact congrArg Sum.inr (heuniq z (by omega))
    · have hod : d % 2 = 1 := by omega
      obtain ⟨a,ha,had⟩ := matching_onto (m:=m-1) (by omega) hod
      obtain ⟨v,hv⟩ := hs a (by omega)
      have hn : v ≠ r := by intro heq; subst v; rw [hroot] at hv; omega
      refine ⟨.inl ⟨v,hn⟩,?_,?_⟩
      · dsimp only
        rw [thin_matching,←hpred,hv]
        exact had
      · intro z hz
        cases z with
        | inl w =>
          rw [thin_matching,←hpred] at hz
          apply congrArg Sum.inl
          apply Subtype.ext
          apply hi
          apply matching_injective (hsml w.val w.property) (hsml v hn)
          simpa [hv,had] using hz
        | inr e =>
          rw [thin_cross hi hb hroot] at hz
          omega

end Math15Source10
#print axioms Math15Source10.singleton_lift
