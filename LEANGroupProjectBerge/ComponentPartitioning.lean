/-
Copyright (c) 2025 Oscar Bryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oscar Bryan, Reuben Brown, Spraeha Jha, A. Basak Kaya, Joshua Render, Lauren Kate Thompson
-/
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

-- We define 'sub' edgesets as sets of edges in the subtype ↑F.edgeSet, the *type* of edges in F
-- This is in order to establish a partition of ↑F.edgeSet into the edgesets of connected components with at least one edge
-- The definition of IsPartition requires that we represent the set being partitioned as a Subtype and not a Set

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



-- A component's edgeSet is the image of its subEdgeSet by the function Subtype.val
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

-- A connected component's subEdgeSet cannot be empty if a vertex inside the component has a neighbour
theorem comp_adj_sub_edgeset_not_empty {x y : V} (h_adj : F.Adj x y) : (F.connectedComponentMk x).subEdgeSet ≠ ∅ := by
  let c := F.connectedComponentMk x
  have : y ∈ c.supp := (SimpleGraph.ConnectedComponent.mem_supp_congr_adj _ h_adj).mp rfl
  have h_eC : s(x,y) ∈ c.edgeSet := ⟨ rfl, this, h_adj⟩
  have h_eF : s(x,y) ∈ F.edgeSet := h_adj
  have : ⟨s(x,y), h_eF⟩ ∈ c.subEdgeSet := by aesop
  aesop


open Setoid

-- The set of nonempty edgesets of components of F form a partition of F's edgeset
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



-- The cardinality of a subgraph M's subEdgeSet in F is equal to the sum of the cardinalities of the intersection of M's subEdgeSet with the edge set of connected components in F
theorem comp_intersection_sum [Finite V] (F: SimpleGraph V) (M : G.Subgraph) : (M.subEdgeSet F).ncard = ∑ᶠ (t : ↑F.edgeSetsPartition), ((M.subEdgeSet F) ∩ ↑t).ncard :=
  Setoid.IsPartition.ncard_eq_finsum (comp_edgesets_partition F) (M.subEdgeSet F)





-- All edges in a component C of F are in E(F), so C's subEdgeSet has a bijection to E(C); their cardinalities are equal.
theorem comp_sub_edgeset_ncard_eq_edgeset (c : F.ConnectedComponent) : c.subEdgeSet.ncard = c.edgeSet.ncard := by
  let f : ↑c.subEdgeSet → ↑c.edgeSet :=
    fun ⟨⟨e, h_eF⟩ , h_eC⟩ => ⟨e, h_eC⟩
  apply Nat.card_eq_of_bijective f
  constructor
  · rintro ⟨⟨a, h_aF⟩ , h_aC⟩ ⟨⟨b, h_bF⟩ , h_bC⟩ h_f_eq
    simp_all only [Subtype.mk.injEq, f]
  · rintro ⟨b, h_bC⟩
    have : b ∈ F.edgeSet := by
      revert b; apply Sym2.ind; intro x y h_b
      exact h_b.2.2
    exists ⟨⟨ b, this ⟩, h_bC⟩


-- A subgraph M's subEdgeSet in a graph F has a bijection to E(M) ∩ E(F). Specifically, their cardinalities are equal.
theorem subgraph_sub_edgeset_ncard_eq_edgeset (M : G.Subgraph) (F : SimpleGraph V) : (M.subEdgeSet F).ncard = (M.edgeSet ∩ F.edgeSet).ncard := by
  let f : ↑(M.subEdgeSet F) → ↑(M.edgeSet ∩ F.edgeSet) :=
    fun ⟨⟨e, h_eF⟩ , h_eM⟩ => ⟨e, ⟨h_eM, h_eF⟩⟩
  apply Nat.card_eq_of_bijective f
  constructor
  · rintro ⟨⟨a, h_aF⟩ , h_aM⟩ ⟨⟨b, h_bF⟩ , h_bM⟩ h_f_eq
    simp_all only [Subtype.mk.injEq, f]
  · rintro ⟨b, ⟨h_bM, h_bF⟩⟩
    exists ⟨⟨b, h_bF⟩ , h_bM⟩


-- Later proofs require manipulations of inequalities and finsums of/as integer values
-- So first we set up theorems to handle casting between Int and Nat in this context
theorem int_nat_le (a b : Nat) : a ≤ b ↔ Int.ofNat a ≤ Int.ofNat b := by
  simp_all only [Int.ofNat_eq_coe, Nat.cast_le]


def intNat : Nat →+ Int where
  toFun := Int.ofNat;
  map_zero' := rfl
  map_add' := by
    intro x y
    simp_all only [Int.ofNat_eq_coe, Nat.cast_add]


theorem finsum_nat_int_cast (α : Sort u) [Finite α] {f : α → Nat} : ∑ᶠ (t : α), Int.ofNat (f t) = Int.ofNat (∑ᶠ (t : α), f t) := by
  have : (Function.support (f ∘ PLift.down)).Finite := by toFinite_tac
  have : ∑ᶠ (t : α), intNat (f t) = intNat (∑ᶠ (t : α), f t) := by
    apply Eq.symm <| AddMonoidHom.map_finsum_plift intNat f this
  aesop


theorem sub_edge_component_intersection {c : F.ConnectedComponent} {E : Set ↑F.edgeSet} (h_Eeq : Subtype.val '' E = c.edgeSet) (M : G.Subgraph) :
    (c.edgeSet ∩ M.edgeSet).ncard = (M.subEdgeSet F ∩ E).ncard := by
  have h_E_val_c: ∀ e : ↑F.edgeSet, e ∈ E → e.val ∈ c.edgeSet := by
    rw[←h_Eeq]
    intro e he
    exact Set.mem_image_of_mem Subtype.val he
  let f : ↑(M.subEdgeSet F ∩ E) → ↑(c.edgeSet ∩ M.edgeSet) :=
    fun ⟨⟨e, h_eF⟩, h_eM, h_eE⟩ => ⟨e, h_E_val_c ⟨e, h_eF⟩ h_eE, h_eM⟩
  apply Eq.symm; apply Nat.card_eq_of_bijective f
  constructor
  · rintro ⟨⟨b, h_bF⟩, ⟨h_bM, h_bE⟩⟩ ⟨⟨a, h_aF⟩, ⟨h_aM, h_aE⟩⟩ h
    simp_all only [Subtype.mk.injEq, f]
  · rintro ⟨e, h_ec, h_eM⟩
    have h_eF : e ∈ F.edgeSet := by revert e; apply Sym2.ind; intro x y h_ec h_eM; exact h_ec.2.2
    have h_eE : ⟨ e, h_eF⟩ ∈ E := by
      obtain ⟨e', h_e'⟩  : ∃e' ∈ E, Subtype.val e'=e := (Set.mem_image Subtype.val E e).mp (h_Eeq ▸ h_ec)
      aesop
    exists ⟨⟨e, h_eF⟩, h_eM, h_eE⟩



-- This is the core of the proof
-- If all components C of F are s.t. |E(C) ∩ E(M)| ≥ |E(C) ∩ E(M')|, then |E(M) ∩ E(F)| ≥ |E(M') ∩ E(F)|
theorem component_intersection_gt [Finite V] (h : ∀ (c : F.ConnectedComponent), (c.edgeSet ∩ M.edgeSet).ncard ≥ (c.edgeSet ∩ M'.edgeSet).ncard) :
    (M'.edgeSet ∩ F.edgeSet).ncard ≤ (M.edgeSet ∩ F.edgeSet).ncard := by
  rw[←subgraph_sub_edgeset_ncard_eq_edgeset M F, ←subgraph_sub_edgeset_ncard_eq_edgeset M' F]
  rw[comp_intersection_sum F M, comp_intersection_sum F M']
  replace h : ∀ (c : F.ConnectedComponent), Int.ofNat (c.edgeSet ∩ M.edgeSet).ncard - Int.ofNat (c.edgeSet ∩ M'.edgeSet).ncard ≥ 0 := by
    intro c
    replace h := (int_nat_le _ _).mp <| h c
    omega
  have : ∑ᶠ (t : ↑F.edgeSetsPartition), (Int.ofNat (M.subEdgeSet F ∩ ↑t).ncard - Int.ofNat (M'.subEdgeSet F ∩ ↑t).ncard) ≥ 0 := by
    apply finsum_induction
    · rfl
    · intros; omega
    · rintro ⟨E, ⟨⟨c, h_Ec_eq⟩ , _ ⟩⟩
      specialize h c
      rw[sub_edge_component_intersection h_Ec_eq M,sub_edge_component_intersection h_Ec_eq M'] at h
      exact h
  rw[finsum_sub_distrib (by toFinite_tac) (by toFinite_tac)] at this
  replace this : ∑ᶠ (i : ↑F.edgeSetsPartition), Int.ofNat (M.subEdgeSet F ∩ ↑i).ncard ≥ ∑ᶠ (i : ↑F.edgeSetsPartition), Int.ofNat (M'.subEdgeSet F ∩ ↑i).ncard := by omega
  replace this := finsum_nat_int_cast ↑F.edgeSetsPartition ▸ finsum_nat_int_cast ↑F.edgeSetsPartition ▸ this
  exact (int_nat_le _ _).mpr this



-- For any subgraphs M, M' of G, E(M) ∩ E(M Δ M') = E(M) \ E(M')
theorem symmdiff_subgraph_intersection_minus {F : SimpleGraph V} (h_F : F = symmDiff M.spanningCoe M'.spanningCoe) :
    M.edgeSet ∩ F.edgeSet = M.edgeSet \ M'.edgeSet := by
  apply Set.ext; apply Sym2.ind; intro x y;
  subst h_F
  apply Iff.intro
  · simp
    intro h_M h_F
    cases h_F <;> aesop
  · simp
    intro h_M h_F
    exact ⟨h_M, by left; aesop⟩



-- If F = M Δ M' and |E(F) ∩ E(M)| ≥ |E(F) ∩ E(M')|, then |E(M)| ≥ |E(M')|
theorem symmdiff_intersection_le [Finite V] (F : SimpleGraph V) (h_F : F = symmDiff M.spanningCoe M'.spanningCoe) (h_M_leq : (M'.edgeSet ∩ F.edgeSet).ncard ≤ (M.edgeSet ∩ F.edgeSet).ncard ) :
    M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
  rw[←Set.ncard_inter_add_ncard_diff_eq_ncard M'.edgeSet M.edgeSet, ←Set.ncard_inter_add_ncard_diff_eq_ncard M.edgeSet M'.edgeSet]
  have h1 : M'.edgeSet ∩ F.edgeSet = M'.edgeSet \ M.edgeSet := symmdiff_subgraph_intersection_minus <| symmDiff_comm M'.spanningCoe M.spanningCoe ▸ h_F
  have h2 : M.edgeSet ∩ F.edgeSet = M.edgeSet \ M'.edgeSet := symmdiff_subgraph_intersection_minus h_F
  have : (M'.edgeSet \ M.edgeSet).ncard ≤ (M.edgeSet \ M'.edgeSet).ncard := by rw[h1, h2] at h_M_leq; exact h_M_leq
  rw[Set.inter_comm M'.edgeSet M.edgeSet]
  omega




-- If |E(M')| > |E(M)| , there exists a connected component C in F=M Δ M' with more edges in M' than M
theorem ex_component_intersection_lt [Finite V] (h_gt : M.edgeSet.ncard < M'.edgeSet.ncard) (h_F : F = symmDiff M.spanningCoe M'.spanningCoe) :
    ∃c : F.ConnectedComponent, (c.edgeSet ∩ M.edgeSet).ncard < (c.edgeSet ∩ M'.edgeSet).ncard := by
  by_contra h
  replace h : ∀c : F.ConnectedComponent, ((c.edgeSet ∩ M.edgeSet).ncard ≥ (c.edgeSet ∩ M'.edgeSet).ncard) := by
    intro c
    simp_all only [not_exists, not_lt, ge_iff_le]
  apply not_le.mpr h_gt;
  apply symmdiff_intersection_le F h_F
  exact component_intersection_gt h
