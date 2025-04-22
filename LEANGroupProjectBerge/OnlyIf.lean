import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph


import LeanGroupProjectBerge.symmDiffIsMatching

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {F : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w x : V}

namespace SimpleGraph
namespace Subgraph


lemma FiniteSubgraphFiniteEdgeSet{M:G.Subgraph}[Finite V]: Finite M.edgeSet := by
  have h1: Fintype (Sym2 M.verts):= by exact Fintype.ofFinite (Sym2 ↑M.verts)
  have h2: DecidableRel M.Adj := by exact Classical.decRel M.Adj
  exact Subtype.finite


lemma FiniteSubgraphencardEqncard{M:G.Subgraph}[Finite V]: M.edgeSet.encard = M.edgeSet.ncard := by
  have h1: Finite M.edgeSet:= by exact FiniteSubgraphFiniteEdgeSet
  have h2: M.edgeSet.encard = M.edgeSet.ncard:= by exact Eq.symm (Set.Finite.cast_ncard_eq h1)
  exact h2

theorem IfBerge{M:G.Subgraph}(h: M.IsMatching)[Finite V]:
(∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M) → ¬ IsMaximumMatching M := by
  intro h1
  obtain ⟨u,h1⟩ := h1
  obtain ⟨v,h1⟩ := h1
  obtain ⟨p,h1⟩ := h1
  intro hc
  obtain ⟨hn,hc⟩ := hc
  let M'' := (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)
  have h3: M'' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe) := by aesop
  let M':= (toSubgraph M'' (m'_is_subgraph_of_g M M'' u v p h3)).induce M''.support
  have hc: ¬(M'.IsMatching ∧ M.edgeSet.encard < M'.edgeSet.encard):= by aesop
  have hc: ¬(M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard):= by
    simp_all only [ not_and, not_lt]
    intro a
    simp_all only [forall_const]
    have hen1: M.edgeSet.encard = M.edgeSet.ncard:= by exact FiniteSubgraphencardEqncard
    have hen2: M'.edgeSet.encard = M'.edgeSet.ncard:= by exact FiniteSubgraphencardEqncard
    aesop
  have hm1: M'.IsMatching:= by exact symmDiff_M_p_is_matching M M' M'' u v u p h h1 h3 rfl
  have hm2: M.edgeSet.ncard < M'.edgeSet.ncard:= by
    have hi: M''.edgeSet.ncard > M.edgeSet.ncard:= by
      exact aug_symm_diff_gt h1
    have hi2: M''.edgeSet.ncard = M'.edgeSet.ncard:= by
      exact ncard_m'_equals_hm M M' M'' u v u u p h h1 h3 rfl
    aesop
  have hmf: M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard := by aesop
  contradiction
