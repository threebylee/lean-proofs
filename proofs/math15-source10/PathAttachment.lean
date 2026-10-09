import AlphaJoin

namespace Math15Source10

def pathEnds (n : ℕ) (e : Fin n) : Fin (n+1) × Fin (n+1) :=
  (⟨e.val,by omega⟩,⟨e.val+1,by omega⟩)

def pathJunction (a b : ℕ) : Fin (a+b+1) := ⟨a,by omega⟩

/-- Literal three-arm tree: arms a,b run along the first path, and c+1
is the new arm attached at their junction. -/
def spiderEnds (a b c : ℕ) := Math15.Labeling.joinEnds (pathJunction a b)
  (0 : Fin (c+1)) (pathEnds (a+b)) (pathEnds c)

theorem attach_at_one {V W E F : Type*} {n m k : ℕ}
    {f : V → ℕ} {g : W → ℕ} {a : E → V × V} {b : F → W × W}
    (hf : Complete n f a) (hg : Complete m g b) (ha : Alpha k f a)
    (hk : 1≤k) (hkn : k≤n) (hkm : k≤m+1) (u : V) (v : W)
    (hu : f u=1) (hv : g v=m+1-k) :
    ∃ F : V ⊕ W → ℕ, Complete (n+m+1) F (Math15.Labeling.joinEnds u v a b) ∧
      F (.inl u)=1 := by
  refine ⟨_,join_complete hf hg ha hkn u v (Or.inl ⟨by omega,by omega⟩),?_⟩
  simp [Math15.Labeling.joinLabel,Math15.Labeling.gap,hu,hk]

/-- Historical exploratory input, now refuted at a=b=4. Retained only to
make the scope of the old conditional theorem explicit. Never a premise
of an unconditional result. Use PathOne.path_interior_one_except44 instead. -/
def PathInteriorOne : Prop := ∀ a b : ℕ, 3≤a → 3≤b →
  ∃ f : Fin (a+b+1) → ℕ, Complete (a+b) f (pathEnds (a+b)) ∧
    Alpha (a/2+b/2) f (pathEnds (a+b)) ∧ f (pathJunction a b)=1

/-- Classical endpoint flexibility, expressed without an unproved declaration. -/
def PathEndpointFlexible : Prop := ∀ (m i : ℕ), i≤m →
  ∃ f : Fin (m+1) → ℕ, Complete m f (pathEnds m) ∧ f 0=i

/-- Historical conditional argument. The PathInteriorOne hypothesis is false
at (4,4); this theorem is retained as an attempt record, not an established
center-one theorem or a premise of the unconditional constructions. -/
theorem spider_center_one_of_paths (hp : PathInteriorOne) (he : PathEndpointFlexible)
    (a b c : ℕ) (ha : 3≤a) (hb : a≤b) (hc : b≤c+1) :
    ∃ f : Fin (a+b+1) ⊕ Fin (c+1) → ℕ,
      Complete (a+b+c+1) f (spiderEnds a b c) ∧ f (.inl (pathJunction a b))=1 := by
  obtain ⟨f,hf,haf,huf⟩ := hp a b ha (by omega)
  have hk : 1≤a/2+b/2 := by omega
  have hkn : a/2+b/2≤a+b := by omega
  have hkc : a/2+b/2≤c+1 := by omega
  obtain ⟨g,hg,hvg⟩ := he c (c+1-(a/2+b/2)) (by omega)
  exact attach_at_one hf hg haf hk hkn hkc (pathJunction a b) 0 huf hvg

end Math15Source10
#print axioms Math15Source10.attach_at_one
#print axioms Math15Source10.spider_center_one_of_paths
