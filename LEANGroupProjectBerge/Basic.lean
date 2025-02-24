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
  ends_unsaturated : u ∉ M.support ∧ v ∉ M.support
  ends_distinct: u ≠ v

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



namespace walk


theorem IfBerge{M : G.Subgraph} (h: M.IsMatching):
∃ u v: V, ∃ p: G.Walk u v, p.IsAugmenting M → ¬ IsMaximumMatching M :=
  sorry

theorem OnlyIfBerge{M: G.Subgraph} (h: M.IsMatching):
IsMaximumMatching M → ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmenting M := by
sorry

theorem BergesTheorem (M : G.Subgraph): IsMaximumMatching M ↔ ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmenting M := by
  apply Iff.intro
  · aesop
  · aesop



theorem VerticeHasUniqueNeighbourIfInAugmentingPath {M:G.Subgraph}{p: } (h1: M.IsMatching):
∀v ∈ V, v∈p.support → ∃!w,  M.adj v w := by
sorry

theorem AugPathUniqueNeighbourInAugPath {M:G.subgraph} {p:}(h1: M.IsMatching):
∀v,w∈V, v∈p.support ∧ M.adj v w → w∈p.support := by
sorry

end walk
