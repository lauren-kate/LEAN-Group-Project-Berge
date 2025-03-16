import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import LEANGroupProjectBerge.Basic
import LEANGroupProjectBerge.MatchingDiff

namespace SimpleGraph



universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M₁ : G.Subgraph}
variable {M₂ : G.Subgraph}


-- any walk in the symmetric difference of two matchings satisfies the alternating condition
theorem match_symmdiff_walk_alt (h_m₁ : M₁.IsMatching) (h_m₂ : M₂.IsMatching) {u v : V} (p : (symmDiff M₁.spanningCoe M₂.spanningCoe).Walk u v) :
    ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M₁.Adj w x ↔ ¬M₁.Adj x y) := by
  let F := symmDiff M₁.spanningCoe M₂.spanningCoe
  intro w x y h_wy_ne h_p_wx h_p_xy
  constructor
  · exact fun h h' => matching_contr h_m₁ h_wy_ne h.symm h'
  · intro h_nadj_xy
    have h_fwx : F.Adj w x := p.adj_of_mem_edges h_p_wx
    have h_fxy : F.Adj x y := p.adj_of_mem_edges h_p_xy
    have h_m₂xy : M₂.Adj x y := by cases h_fxy <;> aesop
    cases h_fwx with
    | inl h => exact h.1
    | inr h => exact False.elim <| matching_contr h_m₂ h_wy_ne h.1.symm h_m₂xy


-- a component containing an isolated vertex counts as an M alternating path
theorem deg_zero_isolated {F : SimpleGraph V} (c : F.ConnectedComponent) (M : G.Subgraph):
    (∃v : V, v ∈ c.supp ∧ (F.neighborSet v).encard = 0) → c.componentAltPath M := by
  intro h
  obtain ⟨v, ⟨h_vc, h_dv0⟩⟩ := h
  replace h_dv0 : F.neighborSet v = ∅ := Set.encard_eq_zero.mp h_dv0
  let P : F.Walk v v := Walk.nil
  exists v, v, P
  constructor
  · have h_p : P.IsPath := P.isPath_iff_eq_nil.mpr rfl
    exact {
    edges_nodup := h_p.edges_nodup
    support_nodup := h_p.support_nodup
    alternates := by aesop }
  · apply Set.ext
    intro x
    apply Iff.intro
    · intro h_xc
      have : v ∈ P.support := by aesop
      exact (c.single_vertex h_vc h_dv0 x h_xc) ▸ this
    · intro h
      exact c.walk_vertex_supp P (by aesop) h
  · apply Set.ext
    intro e
    apply Iff.intro
    · revert e
      apply Sym2.ind
      intro x y h
      have : x = v := (c.single_vertex h_vc h_dv0 x h.left)
      have : y = x := this ▸ (c.single_vertex h_vc h_dv0 y h.2.1)
      exact False.elim <| (F.loopless y) (this ▸ h.2.2)
    · intro h
      exact c.walk_edge_supp P e (by aesop) h




-- quality of life lemmas for dealing with vertices of degree 1 and 2

theorem one_neighbour_iff {F : SimpleGraph V} (v : V) : (F.neighborSet v).encard=1 ↔ ExistsUnique (F.Adj v) := by
  constructor
  · intro h
    obtain ⟨ w, h_w⟩  : ∃w : V, (F.neighborSet v)={w} := Set.encard_eq_one.mp h
    exists w
    constructor
    · show w ∈ F.neighborSet v
      aesop
    · intro y h_y
      change y ∈ F.neighborSet v at h_y
      aesop
  · intro h
    obtain ⟨w, h_w⟩ := h
    have : {w} = F.neighborSet v := by aesop
    rw [←this]
    exact Set.encard_singleton w



def ExistsTwo {α : Sort u} (p : α → Prop) : Prop :=
  ∃a b:α, a≠b ∧ p a ∧ p b ∧ ∀c:α, p c → c=a ∨ c=b


theorem two_neighbours_iff {F : SimpleGraph V} (v : V) : (F.neighborSet v).encard=2 ↔ ExistsTwo (F.Adj v) := by
  constructor
  · intro h
    obtain ⟨ w, x, h_wx, h⟩ := Set.encard_eq_two.mp h
    exists w, x
    constructor; exact h_wx
    constructor; show w ∈ (F.neighborSet v); aesop
    constructor; show x ∈ (F.neighborSet v); aesop
    intro y h_y
    change y ∈ F.neighborSet v at h_y
    aesop
  · intro h
    obtain ⟨ w,x, h_wx, h_eq⟩ := h
    have : {w, x} = F.neighborSet v := by aesop
    rw [←this]
    exact Set.encard_pair h_wx



theorem comp_edge_supp_gt2 [Finite V] (C : G.ConnectedComponent) : (∃x y, x ∈ C.supp ∧ G.Adj x y) → C.supp.ncard ≥ 2 := by
  intro h
  obtain ⟨ x, y, h_xc, h_adj_xy⟩ := h
  have h_yc : y ∈ C.supp := by
    have : G.Reachable y x := Nonempty.intro (Walk.cons h_adj_xy.symm Walk.nil)
    aesop
  exact (Set.one_lt_ncard_iff).mpr ⟨x, y, h_xc, h_yc, by aesop⟩



theorem comp_deg1_supp_gt2 [Finite V] (C : G.ConnectedComponent) (x : V) : x ∈ C.supp → (G.neighborSet x).encard=1 → C.supp.ncard ≥ 2 := by
  intro h_xc h_xd1
  obtain ⟨ y, h ⟩ : ExistsUnique <| G.Adj x := (one_neighbour_iff x).mp h_xd1
  exact comp_edge_supp_gt2 C ⟨x , y, h_xc, h.1⟩




def DegOneOrTwo (c : G.ConnectedComponent) : Prop :=
  (∀v ∈ c.supp, (G.neighborSet v).encard=1 ∨ (G.neighborSet v).encard=2)



--
theorem two_vertex_walk (x y v) (p : G.Walk x v) (h : G.Adj x y) : ExistsUnique (G.Adj x) → ExistsUnique (G.Adj y) → v=x ∨ v=y := by
  intro h_uq_x h_uq_y
  cases p with
  | nil =>
    left; rfl
  | cons h_adj q =>
    rename V => w
    have ih := two_vertex_walk w x v q h_adj.symm
    have : w=y := by
      obtain ⟨ y', _, h_y' ⟩ := h_uq_x
      aesop
    rw[this] at ih
    specialize ih h_uq_y h_uq_x
    aesop



-- this theorem handles the base case of the inductive proof below
theorem comp_vertex_pair (C : G.ConnectedComponent) (h_C2 : C.supp.ncard = 2) :
    ∀x ∈ C.supp, (G.neighborSet x).encard = 1 →
    ∃y ∈ C.supp, y≠ x ∧ (G.neighborSet y).encard = 1 ∧
    ∃P : G.Walk x y, P.IsPath ∧ P.edgeSet = C.edgeSet ∧ P.vertexSet = C.supp := by
  intro x h_xc h_x_d1
  obtain ⟨ y, h_adj_xy, h_y_uq ⟩ := (one_neighbour_iff x).mp h_x_d1
  have h_yc : y ∈ C.supp := have := ConnectedComponent.connectedComponentMk_eq_of_adj h_adj_xy; by aesop
  exists y
  constructor; exact h_yc
  constructor; aesop
  rw[propext (one_neighbour_iff y)]
  have h_yadj_uq : ExistsUnique (G.Adj y) := by
    exists x
    constructor
    exact h_adj_xy.symm
    intro x' h_yx'
    by_contra h_ne
    have h_x'c : x' ∈ C.supp := have := ConnectedComponent.connectedComponentMk_eq_of_adj h_yx'; by aesop
    have h_c_fin : C.supp.Finite := by
      have : C.supp.ncard ≠ 0 := by aesop
      exact Set.finite_of_ncard_ne_zero this
    have : 2 < C.supp.ncard := (Set.two_lt_ncard h_c_fin).mpr ⟨ x, h_xc, y, h_yc, x', h_x'c, by aesop, Ne.symm h_ne, by aesop ⟩
    have : C.supp.ncard ≠ 2 := by omega
    contradiction
  constructor; exact h_yadj_uq
  let P : G.Walk x y := Walk.cons h_adj_xy Walk.nil
  exists P
  have h_p_path : P.IsPath := by
    constructor; constructor
    · aesop
    · have : x≠y := Adj.ne' h_adj_xy.symm
      aesop
  have h_Vpc : P.vertexSet = C.supp := by
    apply Set.ext
    intro v
    apply Iff.intro
    · intro h
      have : v=x ∨ v=y := by change v ∈ [x,y] at h; aesop
      cases this with
      | inr h => exact h ▸ h_yc
      | inl h => exact h ▸ h_xc
    · intro h
      have : G.Reachable x v := ConnectedComponent.exact <| Eq.trans h_xc h.symm
      apply Nonempty.elim this
      intro p
      have : v=x ∨ v=y := two_vertex_walk x y v p h_adj_xy ((propext (one_neighbour_iff x) ▸ h_x_d1)) h_yadj_uq
      show v ∈ [x,y]
      cases this <;> aesop
  have h_Epc : P.edgeSet = C.edgeSet := by
    apply Set.ext
    intro e
    apply Iff.intro
    · revert e
      apply Sym2.ind
      intro u v h
      change s(u,v) ∈ [s(x,y)] at h
      have :s(u,v)=s(x,y) := by aesop
      rw [this]
      apply Set.mem_def.mpr
      show x ∈ C.supp ∧ y ∈ C.supp ∧ G.Adj x y
      aesop
    · revert e
      apply Sym2.ind
      intro u v h
      change u ∈ C.supp ∧ v ∈ C.supp ∧ G.Adj u v at h
      rw [←h_Vpc] at h
      change u ∈ [x,y] ∧ v ∈ [x,y] ∧ G.Adj u v at h
      have h_u_xy: u=x ∨ u=y := by aesop
      cases h_u_xy with
      | inl h_ux =>
        have h_vy : v=y := by aesop
        rw [h_vy, h_ux]
        show s(x,y) ∈ P.edges
        aesop
      | inr h_uy =>
        have h_vx : v=x := by aesop
        rw [h_vx, h_uy]
        show s(y,x) ∈ P.edges
        aesop
  exact ⟨ h_p_path, h_Epc, h_Vpc⟩




-- if all walks from a vertex x must pass through y to reach z, there exists a walk from x containing y but not z
theorem walk_supp_cut_vertex ( w x y z: V) (p : G.Walk w x) (h_yp : y ∈ p.support) (h_yz_ne : y ≠ z) :
    (∀ {a b:V} (w : G.Walk a b), b=x → (z ∈ w.support → y ∈ w.support) ) →
    ∃ q : G.Walk y x, z ∉ q.support := by
  induction p with
  | nil =>
    rename_i x
    intro H
    sorry
  | cons h_adj q ih =>
    rename_i w v x
    let p := Walk.cons h_adj q
    if h : z ∈ q.support then
      intro H
      have := H q rfl h
      specialize ih this
      aesop
    else
      if h1 : y ∈ q.support then
        intro H
        exact ih h1 H
      else
        intro H
        have : w=y := by aesop
        let p' := p.copy this rfl
        have : z ∉ p'.support := by aesop
        exact ⟨ p', this⟩


-- if all walks from z to x contain yz, any walk to x containing z contains yz
theorem walk_required_edge {w x y z : V} ( h: ∀ (w : G.Walk z x), s(y, z) ∈ w.edges) (p : G.Walk w x) : z ∈ p.support → s(y,z) ∈ p.edges :=
  by induction p with
  | nil =>
    sorry
  | cons h_adj q ih =>
    rename_i w v x
    let p := Walk.cons h_adj q
    intro h_z
    specialize ih h
    if h_wz : w=z then
      let p' : G.Walk z x := p.copy h_wz rfl
      have : p.edges = p'.edges := by exact Eq.symm (Walk.edges_copy p h_wz rfl)
      rw[this]
      exact h p'
    else
      have : z ∈ q.support := by aesop
      aesop


-- if all walks from z to x contain yz, and x is reachable from z, there exists a walk from y to x not containing yz
theorem t {x y z : V} : Nonempty (G.Walk z x) → (∀p : G.Walk z x, s(y,z) ∈ p.edges) → ∃ q : G.Walk y x, s(y,z) ∉ q.edges := by
  intro h_p h_a

  apply Nonempty.elim h_p
  intro p

  have : ∀ {a b:V} (w : G.Walk a b), b=x → (z ∈ w.support → y ∈ w.support) := by
    intro a b w h_bx h_z_w
    let w' : G.Walk a x := w.copy rfl h_bx
    have : w'.support = w.support := Walk.support_copy w rfl h_bx
    rw[←this]; rw[←this] at h_z_w
    have := walk_required_edge h_a w' h_z_w
    exact Walk.fst_mem_support_of_mem_edges w' this

  have h_yp : y ∈ p.support := by aesop
  have h_yz_ne : y ≠ z := by sorry

  obtain ⟨ q, h⟩  := walk_supp_cut_vertex _ _ _ _ p h_yp h_yz_ne this
  exists q
  intro h
  have : z ∈ q.support := by exact Walk.snd_mem_support_of_mem_edges q h
  contradiction





theorem edge_del_comp_supp_union {x y : V} (h_adj_xy : G.Adj x y) (H : SimpleGraph V) (h_H : H=G.deleteEdges {s(x,y)} := by try rfl) :
    (G.connectedComponentMk x).supp = (H.connectedComponentMk x).supp ∪ (H.connectedComponentMk y).supp := by
  apply Set.ext
  intro v
  apply Iff.intro
  · intro h_xc

    sorry

  · intro h_u_xy
    cases h_u_xy with
    | inl h_v_cx =>
      have : H.Reachable v x := by aesop
      apply Nonempty.elim this; intro p
      have h_sub : ∀e ∈ p.edges, e ∈ G.edgeSet := by
        apply Sym2.ind; intro a b h_e
        replace h_e : H.Adj a b := by exact Walk.adj_of_mem_edges p h_e;
        aesop
      let p' : G.Walk v x := p.transfer G h_sub
      apply ConnectedComponent.sound
      exact Nonempty.intro p'
    | inr h_v_cy =>
      have : H.Reachable y v := by apply Reachable.symm; aesop
      apply Nonempty.elim this; intro q
      have h_sub : ∀e ∈ q.edges, e ∈ G.edgeSet := by
        apply Sym2.ind; intro a b h_e
        replace h_e : H.Adj a b := by exact Walk.adj_of_mem_edges q h_e
        aesop
      let p : G.Walk x v := Walk.cons h_adj_xy <| q.transfer G h_sub
      apply ConnectedComponent.sound
      exact Nonempty.intro p.reverse





theorem edge_del_comp_edge_union (x y : V) (H : SimpleGraph V) (h : H=G.deleteEdges {s(x,y)} := by try rfl) :
    (G.connectedComponentMk x).edgeSet = (H.connectedComponentMk x).edgeSet ∪ (H.connectedComponentMk y).edgeSet ∪ {s(x,y)} := by sorry






-- if a component only has vertices of deg 1 or 2, and at least one has deg 1, then another vertex has deg 1
-- and there is a path between these two vertices which contains the whole component
theorem deg_one_two_path (n : ℕ) (G : SimpleGraph V) (C : G.ConnectedComponent) (h_neq : n=C.supp.ncard) (h_n2 : n≥2) (h_d : DegOneOrTwo C) :
    (x : V) → x ∈ C.supp → (G.neighborSet x).encard=1 →
    ∃y ∈ C.supp, y≠x ∧ (G.neighborSet y).encard=1 ∧
    ∃P : G.Walk x y, P.IsPath ∧ P.edgeSet=C.edgeSet ∧ P.vertexSet=C.supp := by
  cases n with
  | zero =>
    contradiction
  | succ k  =>
    intro x h_x_inc h_x_deg1
    if h_k : k<2 then --BASE CASE (two vertices)
      replace h_k : k=1 := by omega
      subst h_k; simp at h_neq; clear h_n2
      exact comp_vertex_pair C h_neq.symm x h_x_inc h_x_deg1
    else --INDUCTIVE STEP
      have ih := deg_one_two_path k
      obtain ⟨x', h_adj_xx', h_x'_uq⟩ := (one_neighbour_iff x).mp h_x_deg1
      have h_x'_gd2 : (G.neighborSet x').encard=2 := by sorry

      let H : SimpleGraph V := G.deleteEdges {s(x,x')}
      have h_x'_hd1 : (H.neighborSet x').encard=1 := by sorry

      let D : H.ConnectedComponent := H.connectedComponentMk x'
      have h_D_supp : D.supp = C.supp \ {x} := by sorry
      have h_Dk : k = D.supp.ncard := by sorry
      have h_D_d12 : DegOneOrTwo D := by sorry

      specialize ih H D h_Dk (by omega) h_D_d12 x' rfl h_x'_hd1
      obtain ⟨y, h_yD, h_yx_ne, h_y_hd1, Q, h_q_path, h_Eqd, h_Vqd⟩ := ih
      have h_y_gd1 : (G.neighborSet y).encard = 1 := by sorry

      let Qg : G.Walk x' y := Q.transfer G sorry
      let P : G.Walk x y := Walk.cons h_adj_xx' Qg
      have h_p_path : P.IsPath := by sorry
      have h_Epc : P.edgeSet = C.edgeSet := by sorry
      have h_Vpc : P.vertexSet = C.supp := by sorry

      exact ⟨y, by aesop, by aesop, h_y_gd1, P, h_p_path, h_Epc, h_Vpc⟩




theorem deg_two_cycle [Finite V] (C : G.ConnectedComponent) (h_d2 : ∀v ∈ C.supp, (G.neighborSet v).encard=2) :
    ∃ (x : V) (P : G.Walk x x), P.IsCycle ∧ P.edgeSet=C.edgeSet ∧ P.vertexSet=C.supp := by
  obtain ⟨x, y, h_xc, h_yc, h_adj_xy ⟩ : ∃x y, x ∈ C.supp ∧ y ∈ C.supp ∧ G.Adj x y := by
    sorry
  let H : SimpleGraph V := G.deleteEdges {s(x,y)}
  have h_xd1 : (H.neighborSet x).encard = 1 := by sorry
  have h_yd1 : (H.neighborSet y).encard = 1 := by sorry

  let D : H.ConnectedComponent := H.connectedComponentMk x
  have h_D_d12 : DegOneOrTwo D := by sorry
  have h_D_xyd1 : ∀v ∈ D.supp, (H.neighborSet v).encard=1 ↔ (v=x ∨ v=y) := by sorry
  have h_D2 : D.supp.ncard ≥ 2 := by sorry

  obtain ⟨y', h_y'D, h_y'nx, h_y'd1, P, h_path, h_Epd, h_Vpd ⟩ :=
    deg_one_two_path D.supp.ncard H D rfl h_D2 h_D_d12 x rfl h_xd1

  have h_y_eq : y=y' := by aesop

  let Pg : G.Walk x y' := P.transfer G sorry
  let Q : G.Walk y' y' := Walk.cons (h_y_eq ▸ h_adj_xy.symm) Pg

  exists y', Q
  apply And.intro
  · sorry
  · sorry



-- dumb as fuck
theorem enat_one_or_two (n : ENat) (h : n > 0 ∧ n ≤ 2) : n=1 ∨ n=2 := by
  cases n with
  | top => contradiction
  | coe n' =>
    if h1 : n'=1 then
      aesop
    else
      replace h : n'>0 ∧ n'≤2 := by aesop
      replace h1 : n'≠1 := by aesop
      have : n'=2 := by omega
      aesop




-- every component of the symmetric difference of two matchings is an alternating path (includes isolated vertices) or alternating cycle
theorem matching_symm_diff_alt_paths_cycles [Finite V] (hm₁ : M₁.IsMatching) (hm₂ : M₂.IsMatching) :
  ∀c : (symmDiff M₁.spanningCoe M₂.spanningCoe).ConnectedComponent,
  c.componentAltCycle M₁ ∨ c.componentAltPath M₁ := by
    intro c
    let F := symmDiff M₁.spanningCoe M₂.spanningCoe
    change F.ConnectedComponent at c
    cases em (∀v:V, v ∈ c.supp → (F.neighborSet v).encard > 0) with
    | inr h_ex_v0 => --isolated vertex
      obtain ⟨ v, h_v0 ⟩ := not_forall.mp h_ex_v0
      obtain ⟨ h_vc, h_v0⟩  := Classical.not_imp.mp h_v0
      have : (F.neighborSet v).encard = 0 := by simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero]
      right
      exact deg_zero_isolated c M₁ ⟨v, h_vc, this⟩
    | inl h =>
      if h_d2 : ∀v:V, v ∈ c.supp → (F.neighborSet v).encard = 2 then
        left --CYCLE
        obtain ⟨ x, P, h_cyc, h_Epc, h_Vpc⟩ := deg_two_cycle c h_d2
        exists x, P
        constructor
        · constructor
          · exact h_cyc
          · exact match_symmdiff_walk_alt hm₁ hm₂ P
        · exact h_Vpc.symm
        · exact h_Epc.symm
      else
        right --PATH
        have h_d12 : DegOneOrTwo c := by
          intro x h_xc
          have : (F.neighborSet x).encard ≤ 2 := matching_symm_diff_dg_lt2 hm₁ hm₂ x
          specialize h x h_xc
          exact enat_one_or_two (F.neighborSet x).encard ⟨h , this⟩
        obtain ⟨x, h_xc, h_x_d1⟩ : ∃x ∈ c.supp, (F.neighborSet x).encard = 1 := by
          obtain ⟨ x, h_x ⟩ := not_forall.mp h_d2
          obtain ⟨ h_xc, h_xdn2⟩ := propext Classical.not_imp ▸ h_x
          exists x
          specialize h_d12 x h_xc
          aesop
        have h_c_2 : c.supp.ncard ≥ 2 := comp_deg1_supp_gt2 c x h_xc h_x_d1
        obtain ⟨y, h_yc, h_ynx, h_yd1, P, h_path, h_Epc, h_Vpc ⟩  :=
          deg_one_two_path c.supp.ncard F c rfl h_c_2 h_d12 x h_xc h_x_d1
        exists x, y, P
        constructor
        · constructor
          · exact h_path
          · exact match_symmdiff_walk_alt hm₁ hm₂ P
        · exact h_Vpc.symm
        · exact h_Epc.symm
