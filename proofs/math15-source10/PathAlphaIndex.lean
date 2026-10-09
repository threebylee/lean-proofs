import PathZeroBalanced

namespace Math15Source10

theorem path_alpha_parity {n k : ℕ} {f : Fin (n+1) → ℕ}
    (ha : Alpha k f (pathEnds n)) (i : ℕ) (hi : i≤n) :
    f ⟨i,by omega⟩≤k ↔ (i%2=0 ↔ f 0≤k) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hp := ih (by omega)
    have he := ha ⟨i,by omega⟩
    simp only [pathEnds] at he
    omega

theorem low_class_card_le {V E F : Type*} {n k l : ℕ} {f g : V → ℕ}
    {a : E → V × V} {b : F → V × V}
    (hf : Complete n f a) (hg : Complete n g b) (hk : k≤n)
    (he : ∀v,f v≤k → g v≤l) : k≤l := by
  classical
  let pick (i : Fin (k+1)) : V := Classical.choose (hf.2.2.1 i.val (by omega))
  have hp (i : Fin (k+1)) : f (pick i)=i.val := Classical.choose_spec (hf.2.2.1 i.val (by omega))
  let embed (i : Fin (k+1)) : Fin (l+1) := ⟨g (pick i),by have := he (pick i) (by rw [hp]; omega); omega⟩
  have hinj : Function.Injective embed := by
    intro i j hij
    have hh := hg.1 (congrArg Fin.val hij)
    apply Fin.ext
    rw [←hp i,←hp j,hh]
  have hh := Fintype.card_le_of_injective embed hinj
  simpa using hh

theorem path_alpha_index_unique {n k l r : ℕ} {f g : Fin (n+1) → ℕ}
    (hf : Complete n f (pathEnds n)) (hg : Complete n g (pathEnds n))
    (ha : Alpha k f (pathEnds n)) (hb : Alpha l g (pathEnds n))
    (hk : k≤n) (hl : l≤n) (hr : r≤n)
    (hfr : f ⟨r,by omega⟩≤k) (hgr : g ⟨r,by omega⟩≤l) : k=l := by
  have hpf := path_alpha_parity ha r hr
  have hpg := path_alpha_parity hb r hr
  have he (v : Fin (n+1)) : f v≤k ↔ g v≤l := by
    have hqf := path_alpha_parity ha v.val (by omega)
    have hqg := path_alpha_parity hb v.val (by omega)
    change f v≤k ↔ (v.val%2=0 ↔ f 0≤k) at hqf
    change g v≤l ↔ (v.val%2=0 ↔ g 0≤l) at hqg
    omega
  have h1 := low_class_card_le hf hg hk (fun v => (he v).mp)
  have h2 := low_class_card_le hg hf hl (fun v => (he v).mpr)
  omega

/-- The alpha threshold is forced by the root's position, not an extra
choice hidden in the existential rooted-path theorem. -/
theorem path_zero_index {a b k : ℕ} {f : Fin (a+b+1) → ℕ}
    (ha : 1≤a) (hb : 1≤b) (hk : k≤a+b)
    (hf : Complete (a+b) f (pathEnds (a+b)))
    (hal : Alpha k f (pathEnds (a+b))) (hr : f (pathJunction a b)=0) :
    k=a/2+b/2 := by
  by_cases he : a%2=0
  · have hx := path_alpha_index_unique hf (walecki_complete (a+b)) hal (walecki_alpha (a+b))
      hk (by omega) (show a≤a+b by omega) (by simpa [pathJunction,hr] using (show f (pathJunction a b)≤k by rw [hr]; omega))
      (show walecki (a+b) ⟨a,by omega⟩≤(a+b)/2 by simp [walecki,he]; omega)
    omega
  · have hc := complete_reflect (walecki_complete (a+b))
    have hca := complement_alpha (walecki_complete (a+b)).2.1 (walecki_alpha (a+b)) (show (a+b)/2<a+b by omega)
    have hx := path_alpha_index_unique hf hc hal hca hk (by omega) (show a≤a+b by omega)
      (show f ⟨a,by omega⟩≤k by change f (pathJunction a b)≤k; rw [hr]; omega)
      (show a+b-walecki (a+b) ⟨a,by omega⟩≤a+b-(a+b)/2-1 by simp [walecki,he]; omega)
    omega

theorem path_zero_fixed (a b : ℕ) (ha : 1≤a) (hb : 1≤b) (hex : a≠2 ∨ b≠2) :
    ∃ f : Fin (a+b+1) → ℕ, Complete (a+b) f (pathEnds (a+b)) ∧
      Alpha (a/2+b/2) f (pathEnds (a+b)) ∧ f (pathJunction a b)=0 := by
  obtain ⟨k,f,hk,hf,hal,hr⟩ := pathZero_all a b ha hb hex
  have he := path_zero_index ha hb hk hf hal hr
  subst k
  exact ⟨f,hf,hal,hr⟩

end Math15Source10
#print axioms Math15Source10.path_zero_fixed
