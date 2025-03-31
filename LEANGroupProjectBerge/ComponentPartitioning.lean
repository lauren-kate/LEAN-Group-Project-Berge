import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Setoid.Partition

import LEANGroupProjectBerge.Basic

universe u
variable {V : Type u}
variable {F G : SimpleGraph V}
variable {F G : SimpleGraph V}
variable {M M' : G.Subgraph}




namespace SimpleGraph


namespace ConnectedComponent

def subEdgeSet (c : F.ConnectedComponent) : Set ↑F.edgeSet :=
  setOf ( fun ⟨ e, _ ⟩  => e ∈ c.edgeSet )

end ConnectedComponent


def edgeSetsPartition (F : SimpleGraph V) : Set ( Set ↑F.edgeSet)  :=
  { E : Set ↑F.edgeSet | ∃ c : F.ConnectedComponent, Set.image Subtype.val E = c.edgeSet } \ {∅}


end SimpleGraph


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



open Setoid

theorem comp_edgesets_partition : IsPartition G.edgeSetsPartition := by
  unfold IsPartition
  constructor
  · exact Set.not_mem_diff_of_mem rfl
  · rintro ⟨e, h_e⟩
    revert e; apply Sym2.ind
    intro x y h_e
    let c := G.connectedComponentMk x
    let E' := c.subEdgeSet
    exists E'
    simp
    constructor
    · constructor
      · sorry
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
