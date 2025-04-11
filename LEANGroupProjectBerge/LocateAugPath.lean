
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import LEANGroupProjectBerge.Basic
import LEANGroupProjectBerge.AlternatingProperties
import LEANGroupProjectBerge.ComponentPartitioning
import LEANGroupProjectBerge.PathCycleComponents


universe u
variable {V : Type u}
variable {F G : SimpleGraph V}
variable {M M' : G.Subgraph}


open SimpleGraph


theorem walk_symmdiff_subgraph_sdiff_eq {u v : V} (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u v) : p.edgeSet \ M.edgeSet = p.edgeSet ∩ M'.edgeSet := by
  apply Set.ext; apply Sym2.ind; intro x y; apply Iff.intro
  repeat rintro ⟨h_p, h_m⟩; cases p.adj_of_mem_edges h_p <;> aesop


theorem cycle_comp_M_M'_edges_ncard_eq [Finite V] (c : (symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent) (h_c_altc : c.componentAltCycle M) :
    (c.edgeSet ∩ M.edgeSet).ncard = (c.edgeSet ∩ M'.edgeSet).ncard := by
  let F := symmDiff M.spanningCoe M'.spanningCoe
  obtain ⟨u, p, h_p⟩ := h_c_altc
  have h_pm_inter := alt_cycle_edgeset_inter (h_p.toIsAlternatingCycle)
  have h_p_MuM' : p.edgeSet = (p.edgeSet ∩ M.edgeSet) ∪ (p.edgeSet \ M.edgeSet) := by simp_all only [Set.inter_union_diff]
  have h_disjoint : p.edgeSet.ncard = (p.edgeSet ∩ M.edgeSet).ncard + (p.edgeSet \ M.edgeSet).ncard := by
    rw (occs := .pos [1]) [h_p_MuM']
    have : Disjoint (p.edgeSet ∩ M.edgeSet) (p.edgeSet \ M.edgeSet) := Disjoint.symm Set.disjoint_sdiff_inter
    apply Set.ncard_union_eq this
  have h_symmdiff : p.edgeSet \ M.edgeSet = p.edgeSet ∩ M'.edgeSet := walk_symmdiff_subgraph_sdiff_eq p
  rw [h_p.3, ←h_symmdiff]
  rw [Set.inter_comm, h_disjoint] at h_pm_inter
  omega




theorem matching_symmdiff_alt_path_edgeset_ncard_gt [Finite V] (h_M_match : M.IsMatching) (h_M'_match : M'.IsMatching) (h_e_gt : M'.edgeSet.ncard > M.edgeSet.ncard):
    ∃c:(symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent, c.componentAltPath M ∧ (c.edgeSet ∩ M'.edgeSet).ncard > (c.edgeSet ∩ M.edgeSet).ncard := by
  let F := symmDiff M.spanningCoe M'.spanningCoe
  obtain ⟨c, h_c⟩ := ex_component_intersection_lt h_e_gt <| @rfl _ F
  cases matching_symm_diff_alt_paths_cycles h_M_match h_M'_match c with
  | inl h_cyc =>
    have := cycle_comp_M_M'_edges_ncard_eq c h_cyc
    omega
  | inr h_path => exists c





-- exists an augmenting path in F
theorem matching_symmdiff_gt_aug [Finite V] (h_M_match : M.IsMatching) (h_M'_match : M'.IsMatching) (h_e_gt : M'.edgeSet.ncard > M.edgeSet.ncard):
    ∃ (u v : V) (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u v), p.IsAugmentingPath M := by
  sorry


-- exists an augmenting path in G
theorem matching_not_max_aug [Finite V] (h_M_match : M.IsMatching) (h_M_nmax : ¬M.IsMaximumMatching) :
    ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M := by
  sorry
