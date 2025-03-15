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
  sorry



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






theorem one_neighbour_iff {F : SimpleGraph V} (v : V) : (F.neighborSet v).encard=1 ↔ ExistsUnique (F.Adj v) := by
  sorry


def ExistsTwo {α : Sort u} (p : α → Prop) : Prop :=
  ∃a b:α, a≠b ∧ ∀c:α, p c → c=a ∨ c=b


theorem two_neighbours_iff {F : SimpleGraph V} (v : V) : (F.neighborSet v).encard=2 ↔ ExistsTwo (F.Adj v) := by
  sorry



def DegOneOrTwo (c : G.ConnectedComponent) : Prop :=
  (∀v ∈ c.supp, (G.neighborSet v).encard=1 ∨ (G.neighborSet v).encard=2)



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
    if h_k : k<2 then
      replace h_k : k=1 := by omega
      subst h_k; simp at h_neq; clear h_n2
      sorry --base case (two vertices)
    else
      have ih := deg_one_two_path k
      sorry --inductive step




theorem deg_two_cycle (C : G.ConnectedComponent) (h_d2 : ∀v ∈ C.supp, (G.neighborSet v).encard=2) :
    ∃ (x : V) (P : G.Walk x x), P.IsCycle ∧ P.edgeSet=C.edgeSet ∧ P.vertexSet=C.supp := by
  sorry




-- every component of the symmetric difference of two matchings is an alternating path (includes isolated vertices) or alternating cycle
theorem matching_symm_diff_alt_paths_cycles (hm₁ : M₁.IsMatching) (hm₂ : M₂.IsMatching) :
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
          sorry
        obtain ⟨x, h_xc, h_x_d1⟩ : ∃x ∈ c.supp, (F.neighborSet x).encard = 1 := by
          sorry
        have h_c_2 : c.supp.ncard ≥ 2 := by
          sorry
        obtain ⟨y, h_yc, h_ynx, h_yd1, P, h_path, h_Epc, h_Vpc ⟩  :=
          deg_one_two_path c.supp.ncard F c rfl h_c_2 h_d12 x h_xc h_x_d1
        exists x, y, P
        constructor
        · constructor
          · exact h_path
          · exact match_symmdiff_walk_alt hm₁ hm₂ P
        · exact h_Vpc.symm
        · exact h_Epc.symm
