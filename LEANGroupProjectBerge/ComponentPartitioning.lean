import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Setoid.Partition.Card

import LEANGroupProjectBerge.Basic

universe u
variable {V : Type u}
variable {F G : SimpleGraph V}
variable {M M' : G.Subgraph}




namespace SimpleGraph


namespace ConnectedComponent

def subEdgeSet (c : F.ConnectedComponent) : Set ↑F.edgeSet :=
  setOf ( fun ⟨ e, _ ⟩ => e ∈ c.edgeSet )

end ConnectedComponent


namespace Subgraph

def subEdgeSet (M : G.Subgraph) (F : SimpleGraph V) : Set ↑F.edgeSet :=
  setOf ( fun ⟨ e, _ ⟩ => e ∈ M.edgeSet)

end Subgraph


def edgeSetsPartition (F : SimpleGraph V) : Set ( Set ↑F.edgeSet)  :=
  { E : Set ↑F.edgeSet | ∃ c : F.ConnectedComponent, Set.image Subtype.val E = c.edgeSet } \ {∅}




theorem comp_edgeset_subtype_eq (c : F.ConnectedComponent) : Set.image Subtype.val (c.subEdgeSet) = c.edgeSet := by
  apply Set.ext; apply Sym2.ind; intro x y; apply Iff.intro
  · aesop
  · intro h
    change x ∈ c.supp ∧ y ∈ c.supp ∧ F.Adj x y at h
    unfold Set.image
    show ∃ a ∈ c.subEdgeSet, ↑a=s(x,y)
    have : s(x,y) ∈ F.edgeSet := F.mem_edgeSet.mpr h.2.2
    let a : ↑F.edgeSet := ⟨s(x,y), this⟩
    exists a


theorem comp_adj_sub_edgeset_not_empty {x y : V} (h_adj : F.Adj x y) : (F.connectedComponentMk x).subEdgeSet ≠ ∅ := by
  let c := F.connectedComponentMk x
  have : y ∈ c.supp := (SimpleGraph.ConnectedComponent.mem_supp_congr_adj _ h_adj).mp rfl
  have h_eC : s(x,y) ∈ c.edgeSet := ⟨ rfl, this, h_adj⟩
  have h_eF : s(x,y) ∈ F.edgeSet := h_adj
  have : ⟨s(x,y), h_eF⟩ ∈ c.subEdgeSet := by aesop
  aesop


open Setoid

theorem comp_edgesets_partition (F : SimpleGraph V) : IsPartition F.edgeSetsPartition := by
  unfold IsPartition
  constructor
  · exact Set.not_mem_diff_of_mem rfl
  · rintro ⟨e, h_e⟩
    revert e; apply Sym2.ind
    intro x y h_e
    let c := F.connectedComponentMk x
    let E' := c.subEdgeSet
    exists E'
    simp
    constructor
    · constructor
      · constructor
        · exists c
          exact comp_edgeset_subtype_eq c
        · have : E' ≠ ∅ := comp_adj_sub_edgeset_not_empty h_e
          aesop
      · have : y ∈ c.supp := (SimpleGraph.ConnectedComponent.mem_supp_congr_adj c h_e).mp rfl
        have : s(x,y) ∈ c.edgeSet := ⟨ by aesop, this, h_e ⟩
        aesop
    · intro D h_DP h_eD
      obtain ⟨ ⟨ c', h_c'⟩, _⟩ := h_DP
      have h_ec' : s(x,y) ∈ c'.edgeSet := by
        rw[←h_c']
        exists ⟨s(x,y), h_e⟩
      have : c=c' := by
        obtain ⟨_, _, _⟩ := h_ec'
        aesop
      apply Set.ext; rintro ⟨a, h_a⟩; revert a; apply Sym2.ind; intro u v h_a
      constructor
      · intro h_aD
        have h_ac': s(u,v) ∈ c'.edgeSet := by
          have : s(u,v) ∈ Subtype.val '' D := by
            exists ⟨s(u,v), h_a⟩
          aesop
        rw[←this] at h_ac'
        assumption
      · intro h_aE
        have : s(u,v) ∈ c'.edgeSet := by aesop
        rw[←h_c'] at this
        unfold Set.image at this
        obtain ⟨⟨a', h_a'⟩, h_a'D, h_aa'⟩ := this
        have : a'=s(u,v) := by aesop
        aesop




theorem comp_intersection_sum [Finite V] (F: SimpleGraph V) (M : G.Subgraph) : (M.subEdgeSet F).ncard = ∑ᶠ (t : ↑F.edgeSetsPartition), ((M.subEdgeSet F) ∩ ↑t).ncard :=
  Setoid.IsPartition.ncard_eq_finsum (comp_edgesets_partition F) (M.subEdgeSet F)






theorem comp_sub_edgeset_ncard_eq_edgeset (c : F.ConnectedComponent) : c.subEdgeSet.ncard = c.edgeSet.ncard := by
  let f : ↑c.subEdgeSet → ↑c.edgeSet :=
    fun ⟨⟨e, h_eF⟩ , h_eC⟩ => ⟨e, h_eC⟩
  apply Nat.card_eq_of_bijective f
  constructor
  · unfold Function.Injective
    rintro ⟨⟨a, h_aF⟩ , h_aC⟩ ⟨⟨b, h_bF⟩ , h_bC⟩ h_f_eq
    simp_all only [Subtype.mk.injEq, f]
  · unfold Function.Surjective
    rintro ⟨b ,h_bC⟩
    have : b ∈ F.edgeSet := by
      revert b; apply Sym2.ind; intro x y h_b
      exact h_b.2.2
    exists ⟨⟨ b, this ⟩, h_bC⟩


theorem subgraph_sub_edgeset_ncard_eq_edgeset (M : G.Subgraph) (F : SimpleGraph V) : (M.subEdgeSet F).ncard = (M.edgeSet ∩ F.edgeSet).ncard := by
  sorry




theorem component_intersection_gt [Finite V] (h : ∀ (c : F.ConnectedComponent), (c.edgeSet ∩ M.edgeSet).ncard ≥ (c.edgeSet ∩ M'.edgeSet).ncard) :
    M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
  sorry







variable (h_gt : M.edgeSet.ncard < M'.edgeSet.ncard)
include h_gt

theorem ex_component_intersection_lt [Finite V] : ∃c : F.ConnectedComponent, (c.edgeSet ∩ M.edgeSet).ncard < (c.edgeSet ∩ M'.edgeSet).ncard := by
  by_contra h
  replace h : ∀c : F.ConnectedComponent, ((c.edgeSet ∩ M.edgeSet).ncard ≥ (c.edgeSet ∩ M'.edgeSet).ncard) := by
    intro c
    simp_all only [not_exists, not_lt, ge_iff_le]
  apply not_le.mpr h_gt;
  exact component_intersection_gt h
