import Mathlib.Tactic.Common
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
sorry

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
  --if there exists and edge it must come from either p or M
  --if comes from M, this is a contradiction of p is an augmenting path (ends not unsaturated)
  --if comes from p this is a contradiction of p being a path

--- Lemma for Lauren's node above mine
lemma AugPathUniqueNeighbourInAugPath {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M) :
∀w : V, w∈p.support → ∃! w',(symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj w w' := by
sorry
