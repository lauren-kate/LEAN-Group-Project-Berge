import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.Group.Even
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import LEANGroupProjectBerge.Basic
import LEANGroupProjectBerge.AugmentingEdges


universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {F : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w x : V}

theorem cycle_is_even(M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∀ (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u u ), p.IsCycle → Even p.edgeSet.encard := by
  let F := (symmDiff M.spanningCoe M'.spanningCoe)
  sorry

-- theorem component_is_alt (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
-- ∀(cc : (symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent), (cc.componentAltPath M) ∨ (cc.componentAltCycle M):=
--   sorry

theorem cycle_eq_in_symm_diff [Finite V] (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching) (p : F.Walk u v):
∀ (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u u ), p.IsCycle → (p.edgeSet ∩ M.edgeSet).ncard = (p.edgeSet ∩ M'.edgeSet).ncard := by
  -- intro
  -- let e := s(u, p.getVert 1)
  -- have h1:  p.toDeleteEdges {e} :=
  -- cases p with
  --   | nil => contradiction
  --   | cons h q =>



  -- let q := p.toDeleteEdges {e}

  -- --have h1: s(u, w) ∈ M.edgeSet ∧ s(u, w) ∈ q.edgeSet → s(z, v) ∈ M.edgeSet ∧ s(z, v) ∈ q.edgeSet :=
  -- have h1: ((s(u, q.getVert 1) ∈ M.edgeSet) → q.edges.getLast ∈ M.edgeSet) ∧  ((s(u, q.getVert 1) ∈ M'.edgeSet) → q.edges.getLast ∈ M'.edgeSet):=
  sorry

namespace SimpleGraph
open Classical

theorem m'_iff_not_m (M': SimpleGraph V) (P: G.Walk u v) (hM': M'=(symmDiff M.spanningCoe P.toSubgraph.spanningCoe)) :
∀ (w x: V), s(w, x) ∈ P.toSubgraph.edgeSet → (M'.Adj w x ↔ ¬M.Adj w x):= by
  intro h1 h2 h3
  unfold symmDiff at hM'
  have h4: M'.edgeSet = symmDiff M.spanningCoe.edgeSet P.toSubgraph.spanningCoe.edgeSet := hM' ▸ @symm_diff_edgeset V M.spanningCoe P.toSubgraph.spanningCoe
  have h5: M'.Adj h1 h2 ↔ (M.spanningCoe \ P.toSubgraph.spanningCoe).Adj h1 h2 ∨ (P.toSubgraph.spanningCoe \ M.spanningCoe).Adj h1 h2 := hM' ▸ sup_adj (M.spanningCoe \ P.toSubgraph.spanningCoe) (P.toSubgraph.spanningCoe \ M.spanningCoe) h1 h2
  constructor
  case mp =>
    intro h6
    have h7: ((M.spanningCoe \ P.toSubgraph.spanningCoe).Adj h1 h2) ∨ ((P.toSubgraph.spanningCoe \ M.spanningCoe).Adj h1 h2) := h5.mp h6
    have h8: P.toSubgraph.spanningCoe.Adj h1 h2 := by assumption
    cases h7 with
    | inl h7l =>
      have h9: (M.spanningCoe.Adj h1 h2) ∧ (¬P.toSubgraph.spanningCoe.Adj h1 h2) := (sdiff_adj M.spanningCoe P.toSubgraph.spanningCoe h1 h2).mp h7l
      have h10: ¬P.toSubgraph.spanningCoe.Adj h1 h2 := by aesop
      contradiction
    | inr h7r =>
      have h11: (P.toSubgraph.spanningCoe.Adj h1 h2) ∧ (¬M.spanningCoe.Adj h1 h2) := (sdiff_adj P.toSubgraph.spanningCoe M.spanningCoe h1 h2).mp h7r
      have h12: ¬M.spanningCoe.Adj h1 h2 := by aesop
      assumption
  case mpr =>
    intro h13
    have h14: P.toSubgraph.spanningCoe.Adj h1 h2 ∧ ¬M.spanningCoe.Adj h1 h2 := And.intro h3 h13
    have h15: M'.Adj h1 h2 := by aesop
    assumption
end SimpleGraph





  -- have h1: ∀ (v : p.toSubgraph.support), G.degree = 2 := p.IsCycle


  -- let F := (symmDiff M.spanningCoe M'.spanningCoe)
  -- -- intro p
  -- induction p with
  -- | nil =>
  -- intros
  -- sorry
  -- -- have h1: p.edgeSet.ncard := (p.edgeSet ∩ M.edgeSet).ncard
  -- -- have h2: p.edgeSet.ncard := (p.edgeSet ∩ M'.edgeSet).ncard
  -- -- have hp: (p.edgeSet ∩ M.edgeSet).ncard := 0
  -- -- rfl
  -- | cons h q ih => sorry




theorem component_edges_greater_than (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching) (he: M'.edgeSet.ncard > M.edgeSet.ncard):
∃ (cc: (symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent), (cc.componentAltPath M) ∧ ((cc.edgeSet ∩ M'.edgeSet).ncard > (cc.edgeSet ∩ M.edgeSet).ncard):=
  sorry

theorem exists_aug_path (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∃ (p: (symmDiff M.spanningCoe M'.spanningCoe).Walk u v), (p.IsAugmentingPath M):=
sorry

theorem berge_left (M : G.Subgraph): (M.IsMaximumMatching) → ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M :=
  sorry
