import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.SymmDiff
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Set.Card

import LEANGroupProjectBerge.Basic
import LEANGroupProjectBerge.outsideOfPath


namespace SimpleGraph

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w x y: V}

--Apologies for having every assumption in () not {}, I needed everything explicit whilst writing otherwise I got confused.

open Walk

open Classical

--Placeholder from Josh's node
lemma AugPathUniqueNeighbourInAugPath {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M) :
∀w : V, w∈p.support → ∃! w',(symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj w w' := by
sorry

--p.support is ordered list, everything else is set
--Converting Josh's node to a form that matches what I had.
lemma AugPathUniqueNeighbourInAugPathRewrite {M':SimpleGraph V} {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M) (h3:M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)) :
∀w : V, w∈p.toSubgraph.support → ∃! w',M'.Adj w w' := by
  intro w
  exact
    fun h4 : w∈p.toSubgraph.support =>
    have h9: p.toSubgraph.support ⊆ p.toSubgraph.verts := (p.toSubgraph).support_subset_verts
    have h8: w ∈ p.toSubgraph.verts := by aesop
    have h5: w ∈ p.support := Iff.mp (p.mem_verts_toSubgraph) h8
    have h6: ∃! w',(symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj w w' := AugPathUniqueNeighbourInAugPath h1 h2 w h5
    have h7:  ∃! w',M'.Adj w w' := by aesop
    h7



lemma m'_is_matching_condition [Finite V] (M : G.Subgraph) (M': SimpleGraph V) (u v : V ) (p: G.Walk u v) (h1: M.IsMatching) (h2: p.IsAugmentingPath M) (h3: M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)): ∀ x:V, x ∈ M'.support → ∃! y:V, M'.Adj x y := by
intro x h
exact
  have h4:x ∈ p.toSubgraph.support ∨ x ∈ (M'.support \ p.toSubgraph.support):= (x_in_path_or_not M M' u v x p h3) h
  show ∃! y:V, M'.Adj x y by
    cases h4 with
    | inl hl => exact AugPathUniqueNeighbourInAugPathRewrite h1 h2 h3 x hl
    | inr hr => exact outside_path_unique_neighbour M M' u v p h1 h3 x hr



lemma m'_is_subgraph_of_g_hl [Finite V] (M:G.Subgraph) (x y:V) (h:M.spanningCoe.Adj x y): G.Adj x y :=
  have h1: M.Adj x y := by aesop
  have h2: G.Adj x y := M.adj_sub h1
  h2

lemma m'_is_subgraph_of_g_hr [Finite V] (u v x y: V ) (p: G.Walk u v) (h: p.toSubgraph.spanningCoe.Adj x y) : G.Adj x y :=
  have h1: p.toSubgraph.Adj x y := by aesop
  have h2: G.Adj x y := p.toSubgraph.adj_sub h1
  h2

lemma m'_is_subgraph_of_g [Finite V] (M : G.Subgraph) (M': SimpleGraph V) (u v : V ) (p: G.Walk u v)  (h3: M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)): M' ≤ G  := by
  intro x y
  exact
    fun h4: M'.Adj x y =>
    have h5: s(x,y) ∈ M'.edgeSet := by aesop
    have h6: s(x,y) ∈ M.spanningCoe.edgeSet ∧ s(x,y) ∉ p.toSubgraph.spanningCoe.edgeSet ∨ s(x,y) ∈ p.toSubgraph.spanningCoe.edgeSet ∧ s(x,y) ∉ M.spanningCoe.edgeSet := by aesop
    have h7: s(x,y) ∈ M.spanningCoe.edgeSet ∨ s(x,y) ∈ p.toSubgraph.spanningCoe.edgeSet := by aesop
    have h8: M.spanningCoe.Adj x y ∨ p.toSubgraph.spanningCoe.Adj x y := by aesop
    have h9: G.Adj x y :=
      show G.Adj x y by
        cases h8 with
        | inl hl => exact m'_is_subgraph_of_g_hl M x y hl
        | inr hr => exact m'_is_subgraph_of_g_hr u v x y p hr
    h9




--Induce M'.support removes isolated vertices from toSubgraph
lemma xy_adj_in_m'_and_hm [Finite V] (M hM : G.Subgraph) (M': SimpleGraph V) (u v x y : V ) (p: G.Walk u v) (h3: M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe))(h5: hM = (toSubgraph M' (m'_is_subgraph_of_g M M' u v p h3)).induce M'.support): M'.Adj x y ↔ hM.Adj x y := {
        mp :=
          fun h12: M'.Adj x y =>
          have h13: (toSubgraph M' (m'_is_subgraph_of_g M M' u v p h3)).Adj x y := by aesop
          have h14: x∈ M'.support :=
            have h15: ∃y:V, M'.Adj x y := by aesop
            have h16: x∈ M'.support := Iff.mp M'.mem_support h15
            h15
          have h15: y ∈ M'.support :=
            have h16: M'.Adj y x := Iff.mp (M'.adj_comm x y) h12
            have h17: ∃x:V, M'.Adj y x:= by aesop
            have h18: y∈ M'.support := Iff.mp M'.mem_support h17
            h18
          have h16: hM.Adj x y := by aesop
          h16
        mpr := by aesop
      }


--hM is basically just M' as a subgraph but removing all vertices that don't form edges.
lemma symmDiff_M_p_is_matching [Finite V] (M hM : G.Subgraph) (M': SimpleGraph V) (u v y : V ) (p: G.Walk u v) (h1: M.IsMatching) (h2: p.IsAugmentingPath M) (h3: M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe))(h5: hM = (toSubgraph M' (m'_is_subgraph_of_g M M' u v p h3)).induce M'.support): hM.IsMatching :=
  have h6: ∀x:V, x ∈ hM.verts → ∃! y, hM.Adj x y := by
    intro x
    exact
      (fun h7: x ∈ hM.verts =>
      have h8: x ∈ M'.support := by aesop
      have h9: M'.IsMatchingSimple := by exact m'_is_matching_condition M M' u v p h1 h2 h3
      have h10: ∃! y, M'.Adj x y := by aesop
      have h11: M'.Adj x y ↔ hM.Adj x y := {
        mp :=
          fun h12: M'.Adj x y =>
          have h13: (toSubgraph M' (m'_is_subgraph_of_g M M' u v p h3)).Adj x y := by aesop
          have h14: x∈ M'.support := by aesop
          have h15: y ∈ M'.support :=
            have h16: M'.Adj y x := Iff.mp (M'.adj_comm x y) h12
            have h17: ∃x:V, M'.Adj y x:= by aesop
            have h18: y∈ M'.support := Iff.mp M'.mem_support h17
            h18
          have h16: hM.Adj x y := by aesop
          h16
        mpr := by aesop
      }
      have h12: ∀y:V, (M'.Adj x y ↔ hM.Adj x y) := by
        intro y
        exact (xy_adj_in_m'_and_hm M hM M' u v x y p h3 h5)

      have h13: ∃! y, hM.Adj x y := Iff.mp (existsUnique_congr h12) h10
      h13
      )
  have h7: hM.IsMatching := h6
  h7



lemma forall_xy_adj_in_m'_and_hm [Finite V] (M hM : G.Subgraph) (M': SimpleGraph V) (u v : V ) (p: G.Walk u v) (h3: M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe))(h5: hM = (toSubgraph M' (m'_is_subgraph_of_g M M' u v p h3)).induce M'.support): ∀ x y:V, M'.Adj x y ↔ hM.Adj x y := by
  intro x y
  exact xy_adj_in_m'_and_hm M hM M' u v x y p h3 h5


lemma ncard_m'_equals_hm [Finite V] (M hM : G.Subgraph) (M': SimpleGraph V) (u v x y : V ) (p: G.Walk u v) (h1: M.IsMatching) (h2: p.IsAugmentingPath M) (h3: M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe))(h5: hM = (toSubgraph M' (m'_is_subgraph_of_g M M' u v p h3)).induce M'.support): M'.edgeSet.ncard = hM.edgeSet.ncard :=
  have h6: ∀ x y:V, M'.Adj x y ↔ hM.Adj x y := forall_xy_adj_in_m'_and_hm M hM M' u v p h3 h5
  have h7: ∀ x y:V, s(x,y)∈ M'.edgeSet ↔ s(x,y)∈ hM.edgeSet := by
    intro x y
    exact (
      { mp :=
          fun h8: s(x,y)∈ M'.edgeSet =>
          have h9: M'.Adj x y := h8
          have h10: hM.Adj x y := Iff.mp (forall_xy_adj_in_m'_and_hm M hM M' u v p h3 h5 x y) h9
          have h11: s(x,y)∈ hM.edgeSet := h10
          h11
        mpr :=
          fun h8: s(x,y)∈ hM.edgeSet =>
          have h9: hM.Adj x y := h8
          have h10: M'.Adj x y := Iff.mpr (forall_xy_adj_in_m'_and_hm M hM M' u v p h3 h5 x y) h9
          have h11: s(x,y)∈ M'.edgeSet := h10
          h11
        }
    )

  have h39: ∀ a :  (Sym2 V), a ∈ M'.edgeSet ↔ a ∈ hM.edgeSet := Iff.mpr (Sym2.forall)  h7
  --have h40: M'.edgeSet = hM.edgeSet :=

  have h41: M'.edgeSet ⊆ hM.edgeSet :=
    have h42: ∀ a :  (Sym2 V), a ∈ M'.edgeSet →  a ∈ hM.edgeSet := by
      intro a
      exact Iff.mp (h39 a)
        /-exact (
          have h43: a ∈ M'.edgeSet →  a ∈ hM.edgeSet := Iff.mp (h39 a)
          h43
        )-/

    have h43: M'.edgeSet ⊆ hM.edgeSet := h42
    h43

  have h42: hM.edgeSet ⊆ M'.edgeSet :=
    have h43: ∀ a :  (Sym2 V), a ∈ hM.edgeSet →  a ∈ M'.edgeSet := by
      intro a
      exact Iff.mpr (h39 a)
    have h44: hM.edgeSet ⊆ M'.edgeSet := h43
    h44
  have h43: M'.edgeSet = hM.edgeSet := Set.eq_of_subset_of_subset h41 h42
    --h43
  --Set.eq_of_forall_subset_iff h39


  have hM' : M'.edgeSet.Finite := by toFinite_tac
  have hhM : hM.edgeSet.Finite := by toFinite_tac
  have h44: hM.edgeSet.ncard ≤ M'.edgeSet.ncard := Set.ncard_le_ncard h42 hM'
  have h45: M'.edgeSet.ncard ≤ hM.edgeSet.ncard := Set.ncard_le_ncard h41 hhM
  have h43: M'.edgeSet.ncard = hM.edgeSet.ncard := Nat.le_antisymm h45 h44
  h43
