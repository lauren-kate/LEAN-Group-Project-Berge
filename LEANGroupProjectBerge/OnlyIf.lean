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

--remove everything between lines when links are working

lemma symmDiff_M_p_is_matching (M : G.Subgraph) (u v : V ) (p: G.Walk u v) (h1: M.IsMatching) (h2: p.IsAugmentingPath M): (symmDiff M p.toSubgraph).IsMatching :=
    sorry


theorem aug_symm_diff_gt [Finite V] {u v : V} {p : G.Walk u v} (h : p.IsAugmentingPath M):
  (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard > M.edgeSet.ncard :=
  sorry

--remove everything



lemma SymmDiffSpanningCoeEqSymmDiffofSpanningCoe {H₁ H₂ :G.Subgraph}:
(symmDiff H₁.spanningCoe H₂.spanningCoe) = (symmDiff H₁ H₂).spanningCoe := by
refine SimpleGraph.ext_iff.mpr ?_
have h: ∀x y, (symmDiff H₁.spanningCoe H₂.spanningCoe).Adj x y ↔ (symmDiff H₁ H₂).spanningCoe.Adj x y := by
  intro x y
  simp_all only [spanningCoe_adj]
  apply Iff.intro
  · intro a
    sorry
  · intro a
    refine top_adj.mp ?_
    --have h': x ≠ y:= by exact Adj.ne a
    sorry

aesop


lemma SymmDiffSpanningCoeEqualsMatching [Finite V] {u v : V} {p : G.Walk u v}:
(symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard = (symmDiff M p.toSubgraph).edgeSet.ncard := by
have h3: (symmDiff M p.toSubgraph).edgeSet = (symmDiff M p.toSubgraph).spanningCoe.edgeSet:= by exact rfl
have h4: (symmDiff M p.toSubgraph).spanningCoe.edgeSet = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet:= by
  have hsd: (symmDiff M p.toSubgraph).spanningCoe = symmDiff M.spanningCoe p.toSubgraph.spanningCoe:= by
    exact Eq.symm SymmDiffSpanningCoeEqSymmDiffofSpanningCoe
  aesop_graph
have h5: (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet = (symmDiff M p.toSubgraph).edgeSet:= by aesop
aesop


lemma FiniteSubgraphFiniteEdgeSet{M:G.Subgraph}[Finite V]: Finite M.edgeSet := by
  have h1: Fintype (Sym2 M.verts):= by exact Fintype.ofFinite (Sym2 ↑M.verts)
  have h2: DecidableRel M.Adj := by exact Classical.decRel M.Adj
  exact Subtype.finite


lemma FiniteSubgraphencardEqncard{M:G.Subgraph}[Finite V]: M.edgeSet.encard = M.edgeSet.ncard := by
  have h1: Finite M.edgeSet:= by exact FiniteSubgraphFiniteEdgeSet
  have h2: M.edgeSet.encard = M.edgeSet.ncard:= by exact Eq.symm (Set.Finite.cast_ncard_eq h1)
  exact h2

theorem IfBerge{M:G.Subgraph}{h: M.IsMatching}[Finite V]:
(∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M) → ¬ IsMaximumMatching M := by
  intro h1
  obtain ⟨u,h1⟩ := h1
  obtain ⟨v,h1⟩ := h1
  obtain ⟨p,h1⟩ := h1
  intro hc
  obtain ⟨hn,hc⟩ := hc
  let M':= (symmDiff M p.toSubgraph)
  have hc: ¬(M'.IsMatching ∧ M.edgeSet.encard < M'.edgeSet.encard):= by aesop
  have hc: ¬(M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard):= by
    simp_all only [ not_and, not_lt]
    intro a
    simp_all only [forall_const]
    have hen1: M.edgeSet.encard = M.edgeSet.ncard:= by exact FiniteSubgraphencardEqncard
    have hen2: M'.edgeSet.encard = M'.edgeSet.ncard:= by exact FiniteSubgraphencardEqncard
    aesop
  have hm1: M'.IsMatching:= by exact symmDiff_M_p_is_matching M u v p h h1
  have hm2: M.edgeSet.ncard < M'.edgeSet.ncard:= by
    have hi: (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard > M.edgeSet.ncard:= by
      exact aug_symm_diff_gt h1
    have hi2: (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard = (symmDiff M p.toSubgraph).edgeSet.ncard:= by
      exact SymmDiffSpanningCoeEqualsMatching
    aesop
  have hmf: M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard := by aesop
  contradiction
