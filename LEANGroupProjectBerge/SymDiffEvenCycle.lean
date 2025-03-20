import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.Group.Even
import LEANGroupProjectBerge.Basic

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

theorem component_is_alt (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∀(cc : (symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent), (cc.componentAltPath M) ∨ (cc.componentAltCycle M):=
  sorry

theorem cycle_eq_in_symm_diff(M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∀ (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u u ), p.IsCycle → (p.edgeSet ∩ M.edgeSet).ncard = (p.edgeSet ∩ M'.edgeSet).ncard := by
  let F := (symmDiff M.spanningCoe M'.spanningCoe)
  sorry

theorem component_edges_greater_than (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching) (he: M'.edgeSet.ncard > M.edgeSet.ncard):
∃ (cc: (symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent), (cc.componentAltPath M) ∧ ((cc.edgeSet ∩ M'.edgeSet).ncard > (cc.edgeSet ∩ M.edgeSet).ncard):=
  sorry

theorem exists_aug_path (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∃ (p: (symmDiff M.spanningCoe M'.spanningCoe).Walk u v), (p.IsAugmentingPath M):=
sorry

theorem berge_left (M : G.Subgraph): (M.IsMaximumMatching) → ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M :=
  sorry
