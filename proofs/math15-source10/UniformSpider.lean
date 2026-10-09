import RootedLeafExtension

set_option linter.unusedSimpArgs false
namespace Math15Source10

abbrev RadialV (r n : ℕ) := Option (Fin r × Fin n)
abbrev RadialE (r n : ℕ) := Fin r × Fin n
def radialEnds (r n : ℕ) (e : RadialE r n) : RadialV r n × RadialV r n :=
  (if h : e.2.val=0 then none else some (e.1,⟨e.2.val-1,by omega⟩),some e)
def RadialZero (r n : ℕ) : Prop := ∃ f : RadialV r n → ℕ,
  Complete (r*n) f (radialEnds r n) ∧ f none=0
def radialSide (r n : ℕ) (e : RadialE r n) : Bool := decide (e.2.val%2=1)
theorem radialSide_root (r n : ℕ) (e : RadialE r n) :
    (radialEnds r n e).1=none ∨ (radialEnds r n e).2=none → radialSide r n e=false := by
  intro he
  simp only [radialEnds] at he
  split_ifs at he with h <;> simp_all [radialSide]

def radialDoubleVertex (r n : ℕ) : RadialV r (2*n) → ThinV (none : RadialV r n)
  | none => ⟨(none,false),Or.inl rfl⟩
  | some (j,i) => ⟨(some (j,⟨i.val/2,by omega⟩),decide ((i.val/2+i.val)%2=1)),Or.inr (by simp)⟩
def radialDoubleEdge (r n : ℕ) (e : RadialE r (2*n)) :
    {v : RadialV r n // v≠none} ⊕ RadialE r n :=
  if h : e.2.val%2=0 then .inr (e.1,⟨e.2.val/2,by omega⟩)
  else .inl ⟨some (e.1,⟨e.2.val/2,by omega⟩),by simp⟩

theorem radialDoubleVertex_injective (r n : ℕ) : Function.Injective (radialDoubleVertex r n) := by
  intro v w he
  have hh := congrArg Subtype.val he
  cases v with
  | none => cases w <;> simp_all [radialDoubleVertex]
  | some v =>
    cases w with
    | none => simp [radialDoubleVertex] at hh
    | some w =>
      obtain ⟨j,i⟩ := v; obtain ⟨k,l⟩ := w
      simp only [radialDoubleVertex,Prod.mk.injEq,Option.some.injEq,Fin.mk.injEq] at hh
      obtain ⟨⟨rfl,hi⟩,hb⟩ := hh
      have hil : i=l := by
        apply Fin.ext
        by_cases h1 : (i.val/2+i.val)%2=1 <;> by_cases h2 : (l.val/2+l.val)%2=1 <;>
          simp_all <;> omega
      subst l; rfl

theorem radialDoubleEdge_injective (r n : ℕ) : Function.Injective (radialDoubleEdge r n) := by
  rintro ⟨j,i⟩ ⟨k,l⟩ he
  simp only [radialDoubleEdge] at he
  split_ifs at he <;> simp_all [Subtype.ext_iff,Prod.ext_iff,Fin.ext_iff] <;> omega

theorem radialDouble_endpoints (r n : ℕ) (e : RadialE r (2*n)) :
    (radialDoubleVertex r n (radialEnds r (2*n) e).1,
      radialDoubleVertex r n (radialEnds r (2*n) e).2)=
      thinEnds (radialEnds r n) (radialSide r n) (radialSide_root r n) (radialDoubleEdge r n e) ∨
    (radialDoubleVertex r n (radialEnds r (2*n) e).1,
      radialDoubleVertex r n (radialEnds r (2*n) e).2)=
      ((thinEnds (radialEnds r n) (radialSide r n) (radialSide_root r n) (radialDoubleEdge r n e)).2,
       (thinEnds (radialEnds r n) (radialSide r n) (radialSide_root r n) (radialDoubleEdge r n e)).1) := by
  obtain ⟨j,i⟩ := e
  by_cases hi0 : i.val=0
  · left
    simp [radialEnds,radialDoubleVertex,radialDoubleEdge,radialSide,thinEnds,thinPort,hi0]
  · by_cases he : i.val%2=0
    · left
      simp [radialEnds,radialDoubleVertex,radialDoubleEdge,radialSide,thinEnds,thinPort,hi0,he,
        Prod.ext_iff,Subtype.ext_iff,Fin.ext_iff]
      omega
    · by_cases hp : (i.val/2+i.val)%2=1
      · left
        simp [radialEnds,radialDoubleVertex,radialDoubleEdge,radialSide,thinEnds,hi0,he,hp,
          Prod.ext_iff,Subtype.ext_iff,Fin.ext_iff]
        omega
      · right
        simp [radialEnds,radialDoubleVertex,radialDoubleEdge,radialSide,thinEnds,hi0,he,hp,
          Prod.ext_iff,Subtype.ext_iff,Fin.ext_iff]
        omega

theorem radial_zero_double {r n : ℕ} (hr : 1≤r) (hn : 1≤n) (h : RadialZero r n) :
    RadialZero r (2*n) := by
  obtain ⟨f,hf,h0⟩ := h
  have hm : 1≤r*n := Nat.mul_pos hr hn
  have hroot : r*n-f none=r*n := by rw [h0]; omega
  have hh := complete_reflect (singleton_lift (complete_reflect hf) hm none hroot
    (radialSide r n) (radialSide_root r n))
  have hv : Function.Bijective (radialDoubleVertex r n) := by
    apply bijective_of_injective_equal_card _ (radialDoubleVertex_injective r n)
    rw [hh.card_vertex]
    simp [RadialV]; ring
  have he : Function.Bijective (radialDoubleEdge r n) := by
    apply bijective_of_injective_equal_card _ (radialDoubleEdge_injective r n)
    rw [hh.card_edge]
    simp [RadialE]; ring
  have hc := complete_reindex hh _ hv _ he (radialEnds r (2*n)) (by
    intro e
    rcases radialDouble_endpoints r n e with h | h
    · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
      dsimp only at h1 h2; rw [h1,h2]
    · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
      dsimp only at h1 h2; rw [h1,h2,Nat.dist_comm])
  refine ⟨(fun v => 2*(r*n)-thinLabel (r*n) (fun v => r*n-f v) v) ∘ radialDoubleVertex r n,?_,?_⟩
  · convert hc using 1 <;> ring
  · simp [Function.comp_apply,radialDoubleVertex,thinLabel,h0]

end Math15Source10
#print axioms Math15Source10.radial_zero_double
