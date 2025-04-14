
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




theorem symmdiff_walk_edgeset_ncard_eq [Finite V] {u v : V} (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u v) :
    p.edgeSet.ncard = (p.edgeSet ∩ M.edgeSet).ncard + (p.edgeSet ∩ M'.edgeSet).ncard := by
  rw[←walk_symmdiff_subgraph_sdiff_eq]
  have h_p_MuM' : p.edgeSet = (p.edgeSet ∩ M.edgeSet) ∪ (p.edgeSet \ M.edgeSet) := by simp_all only [Set.inter_union_diff]
  have h_disjoint : p.edgeSet.ncard = (p.edgeSet ∩ M.edgeSet).ncard + (p.edgeSet \ M.edgeSet).ncard := by
    rw (occs := .pos [1]) [h_p_MuM']
    have : Disjoint (p.edgeSet ∩ M.edgeSet) (p.edgeSet \ M.edgeSet) := Disjoint.symm Set.disjoint_sdiff_inter
    apply Set.ncard_union_eq this
  omega


theorem cycle_comp_M_M'_edges_ncard_eq [Finite V] (c : (symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent) (h_c_altc : c.componentAltCycle M) :
    (c.edgeSet ∩ M.edgeSet).ncard = (c.edgeSet ∩ M'.edgeSet).ncard := by
  obtain ⟨u, p, h_p⟩ := h_c_altc
  have h_pm_inter := alt_cycle_edgeset_inter (h_p.toIsAlternatingCycle)
  rw[h_p.3]
  rw[Set.inter_comm, symmdiff_walk_edgeset_ncard_eq] at h_pm_inter
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



theorem walk_nil_empty_edgeset {u v : V} ( p : F.Walk u v) (h_uv : u=v) (h_p : p.IsPath) : p.edgeSet = ∅ := by
  cases p with
  | nil => unfold Walk.edgeSet; aesop
  | cons h_adj q => aesop








-- exists an augmenting path in F
theorem matching_symmdiff_gt_aug [Finite V] (h_M_match : M.IsMatching) (h_M'_match : M'.IsMatching) (h_e_gt : M'.edgeSet.ncard > M.edgeSet.ncard):
    ∃ (u v : V) (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u v), p.IsAugmentingPath M := by
  obtain ⟨c, ⟨⟨u, v, p, h_p⟩, h_cMM'⟩⟩ := matching_symmdiff_alt_path_edgeset_ncard_gt h_M_match h_M'_match h_e_gt
  if h_uv : u=v then
    rw[h_p.edges_eq, walk_nil_empty_edgeset p h_uv h_p.toIsPath] at h_cMM'
    aesop
  else
    have h_p_nnil : p.edges ≠ [] := by cases p <;> aesop
    if h_head : p.edges.head h_p_nnil ∈ M.edgeSet then
      if h_end : p.edges.getLast h_p_nnil ∈ M.edgeSet then
        have := p.alt_ends_match_match h_p.toIsTrail h_p.alternates h_p_nnil h_end h_head
        rw[Set.inter_comm, symmdiff_walk_edgeset_ncard_eq] at this
        rw[h_p.edges_eq] at h_cMM'
        omega
      else
        have := p.alt_ends_match_unmatch h_p.toIsTrail h_p.alternates h_p_nnil h_end h_head
        rw[Set.inter_comm, symmdiff_walk_edgeset_ncard_eq] at this
        rw[h_p.edges_eq] at h_cMM'
        omega
    else
      if h_end : p.edges.getLast h_p_nnil ∈ M.edgeSet then
        have := p.alt_ends_unmatch_match h_p.toIsTrail h_p.alternates h_p_nnil h_end h_head
        rw[Set.inter_comm, symmdiff_walk_edgeset_ncard_eq] at this
        rw[h_p.edges_eq] at h_cMM'
        omega
      else
        have := p.alt_ends_unmatch_unmatch h_p.toIsTrail h_p.alternates h_p_nnil h_end h_head
        sorry -- both end edges unmatched; prove end *vertices* are unsaturated


-- exists an augmenting path in G
theorem matching_not_max_aug [Finite V] (h_M_match : M.IsMatching) (h_M_nmax : ¬M.IsMaximumMatching) :
    ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M := by
  sorry
