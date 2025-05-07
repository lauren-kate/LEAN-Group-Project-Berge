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


theorem two_vertex_component {x y} (h_adj : G.Adj x y) : ExistsUnique (G.Adj x) → ExistsUnique (G.Adj y) →
    (G.connectedComponentMk x).supp = {x, y} := by
  intro h_x_uq h_y_uq
  apply Set.ext; intro v
  apply Iff.intro
  · intro h_v_xc
    have : G.Reachable x v := by apply Reachable.symm; aesop
    apply this.elim; intro p
    have : v=x ∨ v=y := two_vertex_walk x y v p h_adj h_x_uq h_y_uq
    aesop
  · intro h_v_xy
    have : v=x ∨ v=y := by aesop
    cases this with
    | inl h => aesop
    | inr h => rw[h]; exact
      (ConnectedComponent.mem_supp_congr_adj _ h_adj).mp rfl




-- if all walks from a vertex x must pass through y to reach z, there exists a walk from x containing y but not z
theorem walk_supp_cut_vertex ( w x y z: V) (p : G.Walk w x) (h_yp : y ∈ p.support) (h_yz_ne : y ≠ z) :
    (∀ {a b:V} (w : G.Walk a b), b=x → (z ∈ w.support → y ∈ w.support) ) →
    ∃ q : G.Walk y x, z ∉ q.support := by
  induction p with
  | nil =>
    rename_i x
    intro H
    have : y=x := by aesop
    let p := (@Walk.nil _ G x ).copy this.symm rfl
    exists p
    aesop
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
    rename_i x
    intro h_z
    have :z=x := by aesop
    let w : G.Walk z x := (@Walk.nil _ G x).copy this.symm rfl
    specialize h w
    aesop
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
theorem walk_only_reach_through {x y z : V} : Nonempty (G.Walk z x) → (∀p : G.Walk z x, s(y,z) ∈ p.edges) → ∃ q : G.Walk y x, s(y,z) ∉ q.edges := by
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
  have h_yz_ne : y ≠ z := by
    specialize h_a p
    have : G.Adj y z := by exact Walk.adj_of_mem_edges p h_a
    aesop
  obtain ⟨ q, h⟩  := walk_supp_cut_vertex _ _ _ _ p h_yp h_yz_ne this
  exists q
  intro h
  have : z ∈ q.support := by exact Walk.snd_mem_support_of_mem_edges q h
  contradiction



-- given that xy is not in p, prove the condition for transferring p to H := G \ xy
theorem edge_del_walk_transfer {u v x y : V} (p : G.Walk u v) (h_xy : s(x,y) ∉ p.edges) : ∀e ∈ p.edges, e ∈ (G.deleteEdges {s(x,y)}).edgeSet := by
  apply Sym2.ind
  intro a b h_e
  constructor
  · exact Walk.adj_of_mem_edges p h_e
  · have : s(a,b)≠s(x,y) := by
      intro h
      exact h_xy <| h ▸ h_e
    aesop



-- if H = G \ xy, the the vertex set of x's component in G is the union of that of x and y's components in H
theorem edge_del_comp_supp_union {x y : V} (h_adj_xy : G.Adj x y) (H : SimpleGraph V) (h_H : H=G.deleteEdges {s(x,y)} := by try rfl) :
    (G.connectedComponentMk x).supp = (H.connectedComponentMk x).supp ∪ (H.connectedComponentMk y).supp := by
  apply Set.ext
  intro v
  apply Iff.intro
  · intro h_xc
    if h : ∀w : G.Walk x v,  s(x,y) ∈ w.edges then
      right
      have : G.Reachable x v := by apply Reachable.symm; aesop
      rw[Sym2.eq_swap] at h
      obtain ⟨p, h_p⟩ := walk_only_reach_through this h
      apply ConnectedComponent.sound
      exact Nonempty.intro <| (p.transfer H <| h_H ▸ (edge_del_walk_transfer p <| (Sym2.eq_swap ▸ h_p))).reverse
    else
      left
      rw [propext Classical.not_forall] at h
      obtain ⟨p, h_p_xy⟩ := h
      have : ∀e ∈ p.edges, e ∈ H.edgeSet := h_H ▸ edge_del_walk_transfer p h_p_xy
      apply ConnectedComponent.sound
      exact Nonempty.intro <| (p.transfer H this).reverse
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



theorem edge_del_reachable {a b x y : V} (H : SimpleGraph V) (h_H : H=G.deleteEdges {s(x,y)}) :
    H.Reachable a b → G.Reachable a b := by
  intro h_hr
  apply Nonempty.elim h_hr
  intro p
  apply Nonempty.intro
  apply p.transfer G
  apply Sym2.ind; intro u v h_uvp
  have : H.Adj u v:= by exact Walk.adj_of_mem_edges p h_uvp
  aesop


theorem edge_del_adj {a b x y : V} (H : SimpleGraph V) (h_H : H=G.deleteEdges {s(x,y)} ) :
    H.Adj a b → G.Adj a b := by
  aesop


theorem edge_del_comp_edge_union {x y : V} (h_adj_xy : G.Adj x y) (H : SimpleGraph V) (h_H : H=G.deleteEdges {s(x,y)} := by try rfl) :
    (G.connectedComponentMk x).edgeSet = (H.connectedComponentMk x).edgeSet ∪ (H.connectedComponentMk y).edgeSet ∪ {s(x,y)} := by
  apply Set.ext
  intro e
  apply Iff.intro
  · revert e
    apply Sym2.ind
    intro a b h_ab
    let C := G.connectedComponentMk x
    let Dx := H.connectedComponentMk x
    let Dy := H.connectedComponentMk y
    change a ∈ C.supp ∧ b ∈ C.supp ∧ G.Adj a b at h_ab
    obtain ⟨h_ac, h_bc, h_gadj_ab⟩ := h_ab
    have : C.supp = Dx.supp ∪ Dy.supp := edge_del_comp_supp_union h_adj_xy H h_H
    rw [this] at h_ac; rw [this] at h_bc
    if h_ab_n_xy : s(a,b) = s(x,y) then
      aesop
    else
      cases h_ac with
      | inr h_acy =>
        cases h_bc with
        | inr h_bcy => -- A IN Y, B IN Y
          left; right
          exact ⟨h_acy, h_bcy, by aesop⟩
        | inl h_bcx => -- A IN Y, B IN X
          have : H.Adj a b := by aesop
          left; left
          exact ⟨(ConnectedComponent.mem_supp_congr_adj Dx (this.symm)).mp h_bcx, h_bcx, this⟩
      | inl h_acx =>
        cases h_bc with
        | inr h_bcy => -- A IN X, B IN Y
          have : H.Adj a b := by aesop
          left; right
          exact ⟨(ConnectedComponent.mem_supp_congr_adj Dy (this.symm)).mp h_bcy, h_bcy, this⟩
        | inl h_bcx => -- A IN X, B IN X
          left; left
          exact ⟨h_acx, h_bcx, by aesop⟩
  · revert e
    apply Sym2.ind
    intro a b h_ab
    cases h_ab with
    | inl h =>
      cases h with
      | inl h =>
        obtain ⟨h_ac, h_bc, h_adj_ab⟩ := h
        constructor
        · apply ConnectedComponent.sound
          exact edge_del_reachable H h_H <| ConnectedComponent.exact h_ac
        constructor
        · apply ConnectedComponent.sound
          exact edge_del_reachable H h_H <| ConnectedComponent.exact h_bc
        · exact edge_del_adj H h_H h_adj_ab
      | inr h =>
        obtain ⟨h_ac, h_bc, h_adj_ab⟩ := h
        constructor
        · apply ConnectedComponent.sound
          have : G.Reachable a y := edge_del_reachable H h_H <| ConnectedComponent.exact h_ac
          exact Nonempty.elim this (fun p => Nonempty.intro <| (Walk.cons h_adj_xy p.reverse).reverse)
        constructor
        · apply ConnectedComponent.sound
          have : G.Reachable b y := edge_del_reachable H h_H <| ConnectedComponent.exact h_bc
          exact Nonempty.elim this (fun p => Nonempty.intro <| (Walk.cons h_adj_xy p.reverse).reverse)
        · exact edge_del_adj H h_H h_adj_ab
    | inr h =>
      have : s(a,b) = s(x,y) := by aesop
      rw [this]
      have h_xc : x ∈ (G.connectedComponentMk x).supp := rfl
      have h_yc : y ∈ (G.connectedComponentMk x).supp :=
        (ConnectedComponent.mem_supp_congr_adj (G.connectedComponentMk x) h_adj_xy).mp h_xc
      exact ⟨h_xc, h_yc, h_adj_xy⟩
