import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import LEANGroupProjectBerge.Basic
import LEANGroupProjectBerge.MatchingDiff
import LEANGroupProjectBerge.Components

namespace SimpleGraph



universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M₁ : G.Subgraph}
variable {M₂ : G.Subgraph}



-- this theorem handles the base case of the inductive proof further down
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
      have h_C : C=G.connectedComponentMk x := by aesop
      have h_C_fin : C.supp.Finite := by apply Set.finite_of_ncard_pos; omega

      obtain ⟨x', h_adj_xx', h_x'_uq⟩ := (one_neighbour_iff x).mp h_x_deg1
      have h_x'_gd2 : (G.neighborSet x').encard=2 := by sorry

      -- delete xx' to obtain H
      let H : SimpleGraph V := G.deleteEdges {s(x,x')}
      have h_x'_hd1 : (H.neighborSet x').encard=1 := by sorry
      have h_x_hc : (H.connectedComponentMk x).supp = {x} := by sorry

      -- D is the connected component of H containing x'
      let D : H.ConnectedComponent := H.connectedComponentMk x'
      have h_C_Dux : C.supp = {x} ∪ D.supp := h_C ▸ h_x_hc ▸ edge_del_comp_supp_union h_adj_xx' H rfl
      have h_D_fin : D.supp.Finite := by sorry

      have h_x_nd : x ∉ D.supp := sorry
      have h_D_supp : D.supp = C.supp \ {x} := by aesop

      have h_Dk : k = D.supp.ncard := by
        rw [h_C_Dux] at h_neq
        change k+1 = (insert x D.supp).ncard at h_neq
        rw [Set.ncard_insert_of_not_mem h_x_nd h_D_fin] at h_neq
        omega

      have h_D_d12 : DegOneOrTwo D := by sorry

      -- obtain path Q in H from x' to y
      specialize ih H D h_Dk (by omega) h_D_d12 x' rfl h_x'_hd1
      obtain ⟨y, h_yD, h_yx_ne, h_y_hd1, Q, h_q_path, h_Eqd, h_Vqd⟩ := ih
      have h_y_gd1 : (G.neighborSet y).encard = 1 := by sorry

      have h_transcon : ∀e ∈ Q.edges, e ∈ G.edgeSet := by
        apply Sym2.ind; intro a b h_ab
        have : H.Adj a b := by exact Walk.adj_of_mem_edges Q h_ab
        aesop

      -- transfer Q to G and concatenate to P with xx'
      let Qg : G.Walk x' y := Q.transfer G h_transcon
      let P : G.Walk x y := Walk.cons h_adj_xx' Qg
      have h_p_path : P.IsPath := by
        apply (Walk.cons_isPath_iff h_adj_xx' Qg).mpr
        have : Qg.IsPath := by
          apply Walk.IsPath.transfer h_transcon
          exact h_q_path
        constructor; exact this
        intro h
        replace h : x ∈ Q.support := by rw [←Q.support_transfer h_transcon]; exact h
        replace h : x ∈ Q.vertexSet := by exact Set.mem_def.mp h
        rw[h_Vqd] at h
        exact h_x_nd h



      -- prove P and C contain the same edges
      have h_Epc : P.edgeSet = C.edgeSet := by
        have : P.edgeSet = Q.edgeSet ∪ {s(x,x')} := by
          rw[Qg.cons_edgeset h_adj_xx', Q.transfer_edgeset_eq h_transcon]
        have : (H.connectedComponentMk x).edgeSet = ∅ := by
          apply Set.ext; intro e; apply Iff.intro
          · revert e; apply Sym2.ind; intro a b h_ab
            obtain ⟨ h_ac, h_bc, h_ab⟩ := h_ab
            have : a=b := by aesop
            exact False.elim <| H.loopless a <| this ▸ h_ab
          · revert e; apply Sym2.ind; intro a b h_ab
            contradiction
        have : C.edgeSet = D.edgeSet ∪ {s(x,x')} := by
          have := edge_del_comp_edge_union h_adj_xx' H rfl
          aesop
        aesop

      have h_Vpc : P.vertexSet = C.supp := by sorry

      exact ⟨y, by aesop, by aesop, h_y_gd1, P, h_p_path, h_Epc, h_Vpc⟩




theorem deg_two_cycle [Finite V] (C : G.ConnectedComponent) (h_d2 : ∀v ∈ C.supp, (G.neighborSet v).encard=2) :
    ∃ (x : V) (P : G.Walk x x), P.IsCycle ∧ P.edgeSet=C.edgeSet ∧ P.vertexSet=C.supp := by
  -- find two adjacent vertices in C
  obtain ⟨x, y, h_xc, h_yc, h_adj_xy ⟩ : ∃x y, x ∈ C.supp ∧ y ∈ C.supp ∧ G.Adj x y := by
    revert C
    apply ConnectedComponent.ind; intro x h
    specialize h x rfl
    obtain ⟨ y, z, _, h_y, _ ⟩ := (two_neighbours_iff x).mp h
    exists x, y
    constructor; rfl
    constructor
    · exact (ConnectedComponent.mem_supp_congr_adj (G.connectedComponentMk x) h_y).mp rfl
    · exact h_y

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
