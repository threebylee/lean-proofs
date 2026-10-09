import RegularAssembly

namespace Math15Source10
open SimpleGraph

theorem tree_path_length_dist {V : Type*} {G : SimpleGraph V} (ht : G.IsAcyclic)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length=G.dist u v := by
  obtain ⟨q,hq,hl⟩ := p.reachable.exists_path_of_dist
  have he := ht.path_unique (⟨p,hp⟩ : G.Path u v) ⟨q,hq⟩
  have h : p=q := congrArg Subtype.val he
  rwa [h]

theorem tree_path_prefix_dist {V : Type*} {G : SimpleGraph V} (ht : G.IsAcyclic)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ} (hi : i≤p.length) :
    G.dist u (p.getVert i)=i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk (tree_path_length_dist ht hp) (p.isSubwalk_take i)
  simpa [min_eq_left hi] using hh.symm

theorem tree_path_adj_indices {V : Type*} {G : SimpleGraph V} (ht : G.IsAcyclic)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i j : ℕ}
    (hi : i≤p.length) (hj : j≤p.length) (ha : G.Adj (p.getVert i) (p.getVert j)) :
    i+1=j ∨ j+1=i := by
  have hd := ht.dist_eq_dist_add_one_of_adj_of_reachable u ha (p.take i).reachable
  rw [tree_path_prefix_dist ht hp hi,tree_path_prefix_dist ht hp hj] at hd
  omega

theorem two_neighbors_exhaust {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {x a b z : V} (hd : G.degree x≤2) (hab : a≠b)
    (ha : G.Adj x a) (hb : G.Adj x b) (hz : G.Adj x z) : z=a ∨ z=b := by
  classical
  have hs : ({a,b} : Finset V)⊆G.neighborFinset x := by
    intro w hw; simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simpa using ha
    · simpa using hb
  have he : ({a,b} : Finset V)=G.neighborFinset x := by
    apply Finset.eq_of_subset_of_card_le hs
    simpa [hab] using hd
  have hm : z∈({a,b} : Finset V) := by rw [he]; simpa using hz
  simpa using hm

theorem connected_closed_all {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    (s : Set V) (r : V) (hr : r∈s) (hs : ∀x∈s,∀y,G.Adj x y → y∈s) : ∀x,x∈s := by
  intro x
  obtain ⟨p⟩ := hc r x
  have walk_closed {a b : V} (q : G.Walk a b) : a∈s → b∈s := by
    induction q with
    | nil => exact id
    | cons h q ih => intro ha; exact ih (hs _ ha _ h)
  exact walk_closed p hr

theorem rooted_longest_path {V : Type*} [Fintype V] {G : SimpleGraph V} (r : V) :
    ∃ (v : V) (p : G.Walk r v), p.IsPath ∧
      ∀ (w : V) (q : G.Walk r w),q.IsPath → q.length≤p.length := by
  classical
  let s := {n | ∃ (v : V) (p : G.Walk r v),p.IsPath ∧ p.length=n}
  have hs : s.Finite := Set.Finite.subset (Set.finite_le_nat (Fintype.card V))
    (by rintro n ⟨v,p,hp,rfl⟩; exact (hp.length_lt).le)
  obtain ⟨_,⟨⟨v,p,hp,rfl⟩,hmax⟩⟩ := hs.exists_maximal (show s.Nonempty from ⟨0,r,Walk.nil,by simp⟩)
  refine ⟨v,p,hp,?_⟩
  intro w q hq
  have hh := hmax ⟨w,q,hq,rfl⟩
  omega

/-- A finite connected graph of maximum degree two, with a specified endpoint,
is a spanning path. This is the chain fact needed after removing the hubs. -/
theorem degree_two_rooted_spanning_path {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hc : G.Connected) (r : V) (hr : G.degree r≤1)
    (hd : ∀v,G.degree v≤2) : ∃ (v : V) (p : G.Walk r v),p.IsPath ∧ ∀x,x∈p.support := by
  classical
  obtain ⟨v,p,hp,hmax⟩ := rooted_longest_path (G:=G) r
  refine ⟨v,p,hp,?_⟩
  apply connected_closed_all hc {x | x∈p.support} r p.start_mem_support
  intro x hx y hxy
  obtain ⟨i,hix,hi⟩ := p.mem_support_iff_exists_getVert.mp hx
  subst x
  by_cases hilast : i=p.length
  · subst i
    simp only [Walk.getVert_length] at hxy ⊢
    by_contra hy
    have hh := hmax y (p.concat hxy) (hp.concat hy hxy)
    simp only [Walk.length_concat] at hh
    omega
  · have hin : i<p.length := by omega
    by_cases hi0 : i=0
    · subst i
      simp only [Walk.getVert_zero] at hxy
      have ha := p.adj_getVert_succ hin
      simp only [Walk.getVert_zero,zero_add] at ha
      have hy : y=p.getVert 1 := Finset.card_le_one.mp hr y (by simpa using hxy) _ (by simpa using ha)
      rw [hy]
      exact p.getVert_mem_support 1
    · have ha := (p.adj_getVert_succ (show i-1<p.length by omega)).symm
      rw [show i-1+1=i by omega] at ha
      have hb := p.adj_getVert_succ hin
      have hab : p.getVert (i-1)≠p.getVert (i+1) := by
        intro he
        have := hp.getVert_injOn (show i-1≤p.length by omega) (show i+1≤p.length by omega) he
        omega
      rcases two_neighbors_exhaust (hd _) hab ha hb hxy with hy | hy
      · rw [hy]; exact p.getVert_mem_support _
      · rw [hy]; exact p.getVert_mem_support _

end Math15Source10
#print axioms Math15Source10.degree_two_rooted_spanning_path
