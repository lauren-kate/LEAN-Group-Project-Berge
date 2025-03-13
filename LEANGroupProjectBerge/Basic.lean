/-
Copyright (c) 2024 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Cool
-/
import Mathlib.Tactic.Common
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace SimpleGraph

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w: V}


-- as a predicate on walks/subgraphs (structure)
namespace Walk

structure IsAlternatingPath {u v : V} (p : G.Walk u v) (M : G.Subgraph) extends p.IsPath : Prop where
  alternates : ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y)

-- support is not just the set of vertices, it's the domain of the adj relation so this should be correct
structure IsAugmentingPath {u v : V} (p : G.Walk u v) (M : G.Subgraph) extends p.IsAlternatingPath M : Prop where
  ends_unsaturated : u ≠ v ∧ u ∉ M.support ∧ v ∉ M.support

end Walk


-- as a subtype
namespace Subgraph

def augPath {G : SimpleGraph V} (M : G.Subgraph) (u v : V) : Type u :=
  {w : G.Walk u v // w.IsAugmentingPath M}

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


theorem IfBerge{M:G.Subgraph}{h1: M.IsMatching}[Finite V]:
∃ u v: V, ∃ p: G.Walk u v, (p.IsAugmentingPath M) → ¬ IsMaximumMatching M := by
  sorry


theorem OnlyIfBerge{M: G.Subgraph}{h1: M.IsMatching}[Finite V]:
¬IsMaximumMatching M → ∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M := by
sorry

theorem BergesTheorem{M:G.Subgraph} {h1: M.IsMatching} [Finite V]:
IsMaximumMatching M ↔ ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M := by
  apply Iff.intro
  · contrapose
    intro a
    simp_all only [not_exists, not_forall, not_not]
    revert a
    exact IfBerge
  · contrapose
    intro a
    simp_all only [not_exists, not_forall, not_not]
    revert a
    exact OnlyIfBerge


end walk



lemma AugPathUniqueNeighbourInAugPath {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M) :
∀w : V, w∈p.support → ∃! w',(symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj w w' := by
sorry


lemma EndsAugPathMeansNotInM {M :G.Subgraph}{p: G.Walk u v}
(h2: p.IsAugmentingPath M):
∀x ∈ p.support,(x=u ∨ x = v) → x ∉ M.support:= by
intro x hp
· intro huv
  cases huv with
  | inl h =>
    subst x
    exact h2.ends_unsaturated.right.left
  | inr h =>
    subst x
    exact h2.ends_unsaturated.right.right




lemma AlongAugPathButNotInM {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M):
∀ x ∈ p.support, x ∉ M.support → (x=u ∨ x = v):= by
intro x hp hM

--lemma EdgeFromEitherPathOrMatching {x y : V}{M :G.Subgraph}{p: G.Walk u v}[Finite V]
--(h1: M.IsMatching)(h2: p.IsAugmentingPath M)
--(h3:(symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj x y ):
--(M.Adj x y ∧ ¬p.toSubgraph.Adj x y) ∨ (¬ M.Adj x y ∧ p.toSubgraph.Adj x y):= by
--sorry


lemma AugPathMatchingNoNeighbours {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M):
∀x y : V, x ∈ p.support → y ∉ p.support →
  ¬ (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj x y
:= by
let M':=symmDiff M.spanningCoe p.toSubgraph.spanningCoe
intro x y h3 h4
show ¬ M'.Adj x y
by_cases h5: x ∈ M.support
· sorry
· sorry
  -- if there exists and edge it must come from either p or M
  --if comes from M, this is a contradiction of p is an augmenting path (ends not unsaturated)
  --if comes from p this is a contradiction of p being a path, because there would be a
  --repeated vertice



--issue, F is not a matching as there are singelton vertices
--this has already been made by Oscar thank you
