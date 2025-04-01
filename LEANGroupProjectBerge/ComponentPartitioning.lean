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
  · rintro ⟨⟨a, h_aF⟩ , h_aC⟩ ⟨⟨b, h_bF⟩ , h_bC⟩ h_f_eq
    simp_all only [Subtype.mk.injEq, f]
  · rintro ⟨b, h_bC⟩
    have : b ∈ F.edgeSet := by
      revert b; apply Sym2.ind; intro x y h_b
      exact h_b.2.2
    exists ⟨⟨ b, this ⟩, h_bC⟩



theorem subgraph_sub_edgeset_ncard_eq_edgeset (M : G.Subgraph) (F : SimpleGraph V) : (M.subEdgeSet F).ncard = (M.edgeSet ∩ F.edgeSet).ncard := by
  let f : ↑(M.subEdgeSet F) → ↑(M.edgeSet ∩ F.edgeSet) :=
    fun ⟨⟨e, h_eF⟩ , h_eM⟩ => ⟨e, ⟨h_eM, h_eF⟩⟩
  apply Nat.card_eq_of_bijective f
  constructor
  · rintro ⟨⟨a, h_aF⟩ , h_aM⟩ ⟨⟨b, h_bF⟩ , h_bM⟩ h_f_eq
    simp_all only [Subtype.mk.injEq, f]
  · rintro ⟨b, ⟨h_bM, h_bF⟩⟩
    exists ⟨⟨b, h_bF⟩ , h_bM⟩



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
      sorry

  rw[finsum_sub_distrib (by toFinite_tac) (by toFinite_tac)] at this
  replace this : ∑ᶠ (i : ↑F.edgeSetsPartition), Int.ofNat (M.subEdgeSet F ∩ ↑i).ncard ≥ ∑ᶠ (i : ↑F.edgeSetsPartition), Int.ofNat (M'.subEdgeSet F ∩ ↑i).ncard := by omega
  replace this := finsum_nat_int_cast ↑F.edgeSetsPartition ▸ finsum_nat_int_cast ↑F.edgeSetsPartition ▸ this
  exact (int_nat_le _ _).mpr this



theorem symmdiff_subgraph_intersection_minus {F : SimpleGraph V} (h_F : F = symmDiff M.spanningCoe M'.spanningCoe) :
    M.edgeSet ∩ F.edgeSet = M.edgeSet \ M'.edgeSet := by
  sorry


theorem symmdiff_intersection_le [Finite V] (F : SimpleGraph V) (h_F : F = symmDiff M.spanningCoe M'.spanningCoe) (h_M_leq : (M'.edgeSet ∩ F.edgeSet).ncard ≤ (M.edgeSet ∩ F.edgeSet).ncard ) :
    M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
  rw[←Set.ncard_inter_add_ncard_diff_eq_ncard M'.edgeSet M.edgeSet, ←Set.ncard_inter_add_ncard_diff_eq_ncard M.edgeSet M'.edgeSet]
  have h1 : M'.edgeSet ∩ F.edgeSet = M'.edgeSet \ M.edgeSet := symmdiff_subgraph_intersection_minus <| symmDiff_comm M'.spanningCoe M.spanningCoe ▸ h_F
  have h2 : M.edgeSet ∩ F.edgeSet = M.edgeSet \ M'.edgeSet := symmdiff_subgraph_intersection_minus h_F
  have : (M'.edgeSet \ M.edgeSet).ncard ≤ (M.edgeSet \ M'.edgeSet).ncard := by rw[h1, h2] at h_M_leq; exact h_M_leq
  rw[Set.inter_comm M'.edgeSet M.edgeSet]
  omega




variable (h_gt : M.edgeSet.ncard < M'.edgeSet.ncard)
include h_gt

theorem ex_component_intersection_lt [Finite V] (h_F : F = symmDiff M.spanningCoe M'.spanningCoe) :
    ∃c : F.ConnectedComponent, (c.edgeSet ∩ M.edgeSet).ncard < (c.edgeSet ∩ M'.edgeSet).ncard := by
  by_contra h
  replace h : ∀c : F.ConnectedComponent, ((c.edgeSet ∩ M.edgeSet).ncard ≥ (c.edgeSet ∩ M'.edgeSet).ncard) := by
    intro c
    simp_all only [not_exists, not_lt, ge_iff_le]
  apply not_le.mpr h_gt;
  apply symmdiff_intersection_le F h_F
  exact component_intersection_gt h
