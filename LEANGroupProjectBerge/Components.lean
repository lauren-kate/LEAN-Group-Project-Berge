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






theorem one_neighbour {F : SimpleGraph V} (v : V) : (F.neighborSet v).encard=1 ↔ ExistsUnique (F.Adj v) := by
  sorry


def ExistsTwo {α : Sort u} (p : α → Prop) : Prop :=
  ∃a b:α, a≠b ∧ ∀c:α, p c → c=a ∨ c=b


theorem two_neighbours {F : SimpleGraph V} (v : V) : (F.neighborSet v).encard=2 ↔ ExistsTwo (F.Adj v) := by
  sorry




theorem matching_symm_diff_alt_paths_cycles (hm₁ : M₁.IsMatching) (hm₂ : M₂.IsMatching) :
  ∀c : (symmDiff M₁.spanningCoe M₂.spanningCoe).ConnectedComponent,
  c.componentAltCycle M₁ ∨ c.componentAltPath M₁ := by
    intro c
    let F := symmDiff M₁.spanningCoe M₂.spanningCoe
    change F.ConnectedComponent at c
    cases em (∀v:V, v ∈ c.supp → (F.neighborSet v).encard > 0) with
    | inr h_ex_v0 =>
      obtain ⟨ v, h_v0 ⟩ := not_forall.mp h_ex_v0
      obtain ⟨ h_vc, h_v0⟩  := Classical.not_imp.mp h_v0
      have : (F.neighborSet v).encard = 0 := by simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero]
      right
      exact deg_zero_isolated c M₁ ⟨v, h_vc, this⟩
    | inl h =>
      if h : ∀v:V, v ∈ c.supp → (F.neighborSet v).encard = 2 then
        sorry
      else
        sorry
