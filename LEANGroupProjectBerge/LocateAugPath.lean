
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




theorem walk_component_reverse {u v : V } {p : F.Walk u v} {c : F.ConnectedComponent} (h_p : p.IsAltPathComponent M c) :
    p.reverse.IsAltPathComponent M c := by
  let pr := p.reverse
  have h_p_path := h_p.toIsPath
  have : pr.IsPath := (Walk.isPath_reverse_iff p).mpr h_p_path
  constructor; exact ⟨this, p.alt_of_reverse h_p.alternates⟩
  · rw[←p.reverse_vertexset_eq]
    exact h_p.vertices_eq
  · rw[←p.reverse_edgeset_eq]
    exact h_p.edges_eq



open Walk

theorem alt_path_comp_head_unsaturated {u v : V} {p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u v} {c : (symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent}
    (h_p : p.IsAltPathComponent M c) (h_p_nnil : p.edges ≠ []) (h_head : p.edges.head h_p_nnil ∉ M.edgeSet) (h_match : M'.IsMatching) : u ∉ M.support := by
  intro h_contr
  cases p with
  | nil => aesop
  | cons h_adj q =>
    rename V => y
    let p := cons h_adj q
    have h_uy_m : s(u,y) ∉ M.edgeSet := by aesop
    have h_uy_m' : s(u,y) ∈ M'.edgeSet := by
      cases h_adj with
      | inl h =>
        simp at h; aesop
      | inr h =>
        simp at h; aesop
    obtain ⟨z, h_uz⟩ := h_contr
    have h_yz : y≠z := fun h => h_uy_m <| h ▸ h_uz
    have h_uz_m' : s(u,z) ∉ M'.edgeSet := by
      if h : u ∈ M'.verts then
        intro h'
        unfold Subgraph.IsMatching at h_match
        obtain ⟨y', _, h_y'_uq ⟩ := h_match h
        exact h_yz <| Eq.trans (h_y'_uq y h_uy_m') (h_y'_uq z h').symm
      else
        exact fun h' => h <| M'.edge_vert h'
    let F := symmDiff M.spanningCoe M'.spanningCoe
    have h_uz_f : F.Adj u z := by left; aesop
    have h_uz_c : s(u,z) ∈ c.edgeSet := by
      have h_uz_comp_eq: F.connectedComponentMk z = F.connectedComponentMk u := ConnectedComponent.connectedComponentMk_eq_of_adj (adj_symm F h_uz_f)
      have h_u_c : u ∈ c.supp := h_p.vertices_eq ▸ p.start_mem_support
      have h_z_c : z ∈ c.supp := by unfold ConnectedComponent.supp; rw[←h_u_c]; exact h_uz_comp_eq
      exact ⟨h_u_c, h_z_c, h_uz_f⟩
    rw[h_p.edges_eq] at h_uz_c
    have : u ∈ q.support := @fst_mem_support_of_mem_edges _ _ u z _ _ q (by cases (@List.mem_cons _ s(u,y) q.edges s(u,z)).mp h_uz_c <;> aesop)
    have : ¬p.support.Nodup  := List.not_nodup_cons_of_mem this
    exact this h_p.support_nodup



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
        exists u, v, p
        have h_u_unsat : u ∉ M.support := alt_path_comp_head_unsaturated h_p h_p_nnil h_head h_M'_match
        have h_v_unsat : v ∉ M.support := by
          have : p.reverse.edges ≠ [] := by aesop
          apply alt_path_comp_head_unsaturated (walk_component_reverse h_p) this
          simp; aesop;
          exact h_M'_match
        exact ⟨h_p.toIsAlternatingPath, h_uv, h_u_unsat, h_v_unsat⟩



-- exists an augmenting path in G
theorem matching_not_max_aug [Finite V] (h_M_match : M.IsMatching) (h_M_nmax : ¬M.IsMaximumMatching) :
    ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M := by
  obtain ⟨M', h_M'_match, h_M'_gt⟩ := not_and_not_right.mp h_M_nmax h_M_match
  have : ∃ (u v : V) (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u v), p.IsAugmentingPath M := by
    apply matching_symmdiff_gt_aug h_M_match h_M'_match
    rw[←(@Set.Finite.cast_ncard_eq _ M.edgeSet (by toFinite_tac)), ←(@Set.Finite.cast_ncard_eq _ M'.edgeSet (by toFinite_tac))] at h_M'_gt
    simp_all only [Nat.cast_lt, gt_iff_lt]
  obtain ⟨u, v, p, h_augF⟩ := this
  have : ∀ e ∈ (symmDiff M.spanningCoe M'.spanningCoe).edgeSet, e ∈ G.edgeSet := by
    apply Sym2.ind
    intro x y h_eF
    cases h_eF with
    | inl h => simp_all [M.adj_sub]
    | inr h => simp_all [M'.adj_sub]
  have h_transcon : ∀ e ∈ p.edges, e ∈ G.edgeSet := by apply Sym2.ind; intro x y h_xy; exact this s(x,y) <| p.adj_of_mem_edges h_xy
  let pg := p.transfer G h_transcon
  exists u, v, pg
  constructor
  · use h_augF.toIsPath.transfer h_transcon
    rw[Walk.edges_transfer]
    exact h_augF.alternates
  · exact h_augF.ends_unsaturated
