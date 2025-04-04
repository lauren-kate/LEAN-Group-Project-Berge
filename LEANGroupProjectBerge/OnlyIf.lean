import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import LeanGroupProjectBerge.Basic

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {F : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w x : V}

namespace SimpleGraph
namespace Subgraph
lemma symmDiff_M_p_is_matching (M : G.Subgraph) (u v : V ) (p: G.Walk u v) (h1: M.IsMatching) (h2: p.IsAugmentingPath M): (symmDiff M p.toSubgraph).IsMatching :=
    sorry


theorem aug_symm_diff_gt [Finite V] {u v : V} {p : G.Walk u v} (h : p.IsAugmentingPath M):
  (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard > M.edgeSet.ncard :=
  sorry

lemma SymDiffSpanningCoeEqualsMatching [Finite V] {u v : V} {p : G.Walk u v}
(h1: M.IsMatching)(h2 : p.IsAugmentingPath M):
(symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard = (symmDiff M p.toSubgraph).edgeSet.ncard := by
sorry



theorem IfBerge{M:G.Subgraph}{h: M.IsMatching}[Finite V]:
(∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M) → ¬ IsMaximumMatching M := by
  intro h1
  obtain ⟨u,h1⟩ := h1
  obtain ⟨v,h1⟩ := h1
  obtain ⟨p,h1⟩ := h1
  intro hc
  obtain ⟨hn,hc⟩ := hc
  let M':= (symmDiff M p.toSubgraph)
  have hc: ¬(M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard):= by sorry
  have hm1: M'.IsMatching:= by exact symmDiff_M_p_is_matching M u v p h h1
  have hm2: M.edgeSet.ncard < M'.edgeSet.ncard:= by
    have hi: (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard > M.edgeSet.ncard:= by
      exact aug_symm_diff_gt h1
    have hi2: (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard = (symmDiff M p.toSubgraph).edgeSet.ncard:= by
      exact SymDiffSpanningCoeEqualsMatching h h1
    aesop
  have hmf: M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard := by aesop
  contradiction
