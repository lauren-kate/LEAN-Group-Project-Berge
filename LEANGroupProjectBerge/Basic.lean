/-
Copyright (c) 2024 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Cool
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace SimpleGraph

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w: V}


-- as a predicate on walks/subgraphs (structure)
namespace Walk

structure IsAlternating {u v : V} (p : G.Walk u v) (M : G.Subgraph) extends p.IsPath : Prop where
  alternates : ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y)

-- support is not just the set of vertices, it's the domain of the adj relation so this should be correct
structure IsAugmenting {u v : V} (p : G.Walk u v) (M : G.Subgraph) extends p.IsAlternating M : Prop where
  ends_unsaturated : u ≠ v ∧ u ∉ M.support ∧ v ∉ M.support

end Walk


-- as a subtype
namespace Subgraph

def augPath {G : SimpleGraph V} (M : G.Subgraph) (u v : V) : Type u :=
  {w : G.Walk u v // w.IsAugmenting M}

end Subgraph


--Added maximal matching for completeness' sake with maximum matchings (maximum and maximal go hand in hand I feel) - we dont need for Berge's
def IsMaximalMatching (M : G.Subgraph): Prop :=
  M.IsMatching ∧
  (¬∃ v w, v ∉ M.support ∧ w ∉ M.support ∧ G.Adj v w)

def IsMaximumMatching (M : G.Subgraph): Prop :=
  M.IsMatching
  ∧ (¬∃ N : G.Subgraph, N.IsMatching ∧ M.edgeSet.encard < N.edgeSet.encard)

lemma IfMaximalMatchingThenMatching (M:G.Subgraph):
IsMaximalMatching M -> M.IsMatching := by
  intro h
  obtain ⟨h1,h2⟩ := h
  exact h1

lemma IfMaximumMatchingThenMatching (M:G.Subgraph):
IsMaximumMatching M -> M.IsMatching := by
  intro h
  obtain ⟨h1,h2⟩ := h
  exact h1


namespace walk


theorem IfBerge{M : G.Subgraph}:
∃ u v: V, ∃ p: G.Walk u v, (p.IsAugmenting M) → ¬ IsMaximumMatching M := by
  sorry


theorem OnlyIfBerge{M: G.Subgraph}:
¬IsMaximumMatching M → ∃ u v: V, ∃ p: G.Walk u v, p.IsAugmenting M := by
sorry

theorem BergesTheorem{M : G.Subgraph} {h: M.IsMatching}: IsMaximumMatching M ↔ ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmenting M := by
  apply Iff.intro
  · contrapose
    intro a
    simp_all only [not_exists, not_forall, not_not]
    revert a
    sorry
  · contrapose
    intro a
    simp_all only [not_exists, not_forall, not_not]
    revert a
    exact OnlyIfBerge


end walk

theorem VerticeHasUniqueNeighbourIfInAugmentingPath {M:G.Subgraph}{p:G.Walk u v}
(h1: M.IsMatching)(h2:p.IsAugmenting M ):
∀{w}, w∈p.support → ∃!w' : M.verts ,  M.adj w w' := by
sorry

theorem AugPathUniqueNeighbourInAugPath {M:G.Subgraph}{p: G.Walk u v}
(h1: M.IsMatching)(h2: p.IsAugmenting M):
∀w' w : V, w'∈p.support ∧ M.adj w' w → w∈p.support := by
sorry
