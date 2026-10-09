import PathBlocks

namespace Math15Source10

def LowEndpoint (n x : ℕ) : Prop := ∃ f : Fin (n+1) → ℕ,
  Complete n f (pathEnds n) ∧ Alpha (n/2) f (pathEnds n) ∧ f 0=x

def prefixLabel (r m : ℕ) (g : Fin (m+1) → ℕ) : Fin (r+m+1+1) → ℕ :=
  Math15.Labeling.joinLabel (r/2) (m+1) (walecki r) (fun v => m-g v) ∘ concatVertex r m

theorem prefix_complete (r m : ℕ) (g : Fin (m+1) → ℕ)
    (hg : Complete m g (pathEnds m)) (hkm : r/2≤m) (hr : g 0=r/2) :
    Complete (r+m+1) (prefixLabel r m g) (pathEnds (r+m+1)) := by
  apply concat_complete
  apply join_complete (walecki_complete r) (complete_reflect hg) (walecki_alpha r) (by omega) 0 0
  apply Or.inl
  simp only [walecki,Fin.val_zero,Nat.zero_mod,Nat.zero_div,↓reduceIte]
  constructor
  · omega
  · dsimp only; rw [hr]; omega

theorem prefix_alpha (r m : ℕ) (g : Fin (m+1) → ℕ)
    (hg : Complete m g (pathEnds m)) (ha : Alpha (m/2) g (pathEnds m))
    (hm : 0<m) (hkm : r/2≤m/2) (hr : g 0=r/2) :
    Alpha (r/2+m-m/2) (prefixLabel r m g) (pathEnds (r+m+1)) := by
  have hk : m/2<m := by omega
  have hh := concat_alpha (join_alpha (walecki_alpha r)
    (complement_alpha hg.2.1 ha hk) (show m-m/2-1≤m by omega)
    (0 : Fin (r+1)) (0 : Fin (m+1)) (by simp [walecki]) (by change m-m/2-1<m-g 0; rw [hr]; omega))
  convert hh using 1 <;> omega

theorem prefix_first_even (x m : ℕ) (g : Fin (m+1) → ℕ) :
    prefixLabel (2*x) m g 0=x := by
  simp [prefixLabel,concatVertex,Math15.Labeling.joinLabel,Math15.Labeling.gap,walecki]

theorem prefix_first_odd (x m : ℕ) (g : Fin (m+1) → ℕ) :
    prefixLabel (2*x+1) m g 0=x+m+2 := by
  simp [prefixLabel,concatVertex,Math15.Labeling.joinLabel,Math15.Labeling.gap,walecki,
    show (2*x+1)/2=x by omega]
  split_ifs <;> omega

theorem lowEndpoint_odd_prefix (x m : ℕ) (h : LowEndpoint m x) (hm : 0<m) (hx : x≤m/2) :
    LowEndpoint (2*x+m+1) x := by
  obtain ⟨g,hg,ha,hr⟩ := h
  refine ⟨prefixLabel (2*x) m g,prefix_complete _ _ _ hg (by omega) (by simpa using hr),?_,prefix_first_even x m g⟩
  convert prefix_alpha (2*x) m g hg ha hm (by omega) (by simpa using hr) using 1 <;> omega

theorem lowEndpoint_even_prefix (x m : ℕ) (h : LowEndpoint m x)
    (hm : m%2=1) (hx : x≤m/2) : LowEndpoint (2*x+1+m+1) x := by
  obtain ⟨g,hg,ha,hr⟩ := h
  have hc := prefix_complete (2*x+1) m g hg (by omega) (by omega)
  have hal := prefix_alpha (2*x+1) m g hg ha (by omega) (by omega) (by omega)
  refine ⟨fun v => 2*x+1+m+1-prefixLabel (2*x+1) m g v,complete_reflect hc,?_,?_⟩
  · convert complement_alpha hc.2.1 hal (by omega) using 1 <;> omega
  · dsimp only; rw [prefix_first_odd]; omega

theorem lowEndpoint_reverse {n x : ℕ} (h : LowEndpoint n (n/2-x)) (hx : x≤n/2) :
    LowEndpoint n x := by
  obtain ⟨f,hf,ha,hr⟩ := h
  refine ⟨reverseLabel n (n/2) f,reverse_complete hf ha (by omega),reverse_alpha hf.2.1 ha,?_⟩
  simp only [reverseLabel,hr]; split_ifs <;> omega

/-- Constructive alpha-path endpoint theorem. The excluded case is a path
with 4x edges and endpoint x>0. The proof uses a shorter alternating block
extension; n=6x+1 is handled by an even block instead. -/
theorem lowEndpoint_all (n x : ℕ) (hx : x≤n/2) (hex : x=0 ∨ n≠4*x) : LowEndpoint n x := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    have hsmall (y : ℕ) (hy : 2*y≤n/2) (hey : y=0 ∨ n≠4*y) : LowEndpoint n y := by
      by_cases hz : y=0
      · subst y; exact ⟨walecki n,walecki_complete n,walecki_alpha n,by simp [walecki]⟩
      · have hn : n≠4*y := hey.resolve_left hz
        by_cases hspecial : n=6*y+1
        · have hm : 4*y-1<n := by omega
          have htail := ih (4*y-1) hm y (by omega) (Or.inr (by omega))
          have hh := lowEndpoint_even_prefix y (4*y-1) htail (by omega) (by omega)
          have heq : 2*y+1+(4*y-1)+1=n := by omega
          simpa only [heq] using hh
        · have hm : n-2*y-1<n := by omega
          have htail := ih (n-2*y-1) hm y (by omega) (Or.inr (by omega))
          have hh := lowEndpoint_odd_prefix y (n-2*y-1) htail (by omega) (by omega)
          have heq : 2*y+(n-2*y-1)+1=n := by omega
          simpa only [heq] using hh
    by_cases hlow : 2*x≤n/2
    · exact hsmall x hlow hex
    · apply lowEndpoint_reverse _ hx
      apply hsmall (n/2-x) (by omega)
      right
      rcases hex with hex | hex
      · omega
      · omega

/-- Endpoint flexibility also covers the two alpha exceptions by an odd
block whose remaining endpoint lies in the opposite bipartition class. -/
theorem path_endpoint_flexible : PathEndpointFlexible := by
  intro n x hx
  have hlow (y : ℕ) (hy : y≤n/2) :
      ∃ f : Fin (n+1) → ℕ, Complete n f (pathEnds n) ∧ f 0=y := by
    by_cases he : y=0 ∨ n≠4*y
    · obtain ⟨f,hf,_,hr⟩ := lowEndpoint_all n y hy he
      exact ⟨f,hf,hr⟩
    · have hn : n=4*y := by omega
      have hp : 0<y := by omega
      obtain ⟨g,hg,_,hr⟩ := lowEndpoint_all (2*y-1) (y-1) (by omega) (by omega)
      let gg : Fin (2*y-1+1) → ℕ := fun v => 2*y-1-g v
      have hgg : gg 0=y := by dsimp [gg]; rw [hr]; omega
      have hc := prefix_complete (2*y) (2*y-1) gg (complete_reflect hg) (by omega) (by simpa using hgg)
      have hf := prefix_first_even y (2*y-1) gg
      have heq : 2*y+(2*y-1)+1=n := by omega
      exact heq ▸ ⟨_,hc,hf⟩
  by_cases hlo : x≤n/2
  · exact hlow x hlo
  · obtain ⟨f,hf,hr⟩ := hlow (n-x) (by omega)
    exact ⟨fun v => n-f v,complete_reflect hf,by dsimp only; rw [hr]; omega⟩

end Math15Source10
#print axioms Math15Source10.lowEndpoint_all
#print axioms Math15Source10.path_endpoint_flexible
