import Mathlib.Tactic.Common
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph


import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.SymmDiff
import Mathlib.Logic.ExistsUnique
import LeanGroupProjectBerge.Basic


universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {F : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w x y: V}



lemma EndsAugPathMeansNotInM {M :G.Subgraph}{p: G.Walk u v}
(h2: p.IsAugmentingPath M):
∀x ∈ p.support,(x=u ∨ x = v) → x ∉ M.support:= by
intro x hp
intro huv
cases huv with
  | inl h =>
    subst x
    exact h2.ends_unsaturated.right.left
  | inr h =>
    subst x
    exact h2.ends_unsaturated.right.right


lemma EndsNotConnectedToMatching {M :G.Subgraph}{p: G.Walk u v}
(h1: p.IsAugmentingPath M) (h2: x=u ∨ x = v):
¬M.Adj x y:= by
  intro a
  have h3: x ∈ M.support := by
    refine (SimpleGraph.Subgraph.mem_support M).mpr ?_
    use y
  cases h2 with
  | inl h2u =>
    subst x
    have h4: u ∉ M.support:= by exact h1.ends_unsaturated.right.left
    contradiction
  | inr h2v =>
    subst x
    have h4: v ∉ M.support:= by exact h1.ends_unsaturated.right.right
    contradiction


lemma PathNotConnectedToOutsideOfPath{p: G.Walk u v}
(h2: y ∉ p.support):
¬p.toSubgraph.Adj x y := by
  have h3: y ∉ p.toSubgraph.support:= by
    have h4: y ∈ p.toSubgraph.verts ↔ y ∈ p.support := by exact SimpleGraph.Walk.mem_verts_toSubgraph p
    have h5: p.toSubgraph.support ⊆ p.toSubgraph.verts:= by exact SimpleGraph.Subgraph.support_subset_verts p.toSubgraph
    have h6: y ∈ p.toSubgraph.support → y ∈ p.toSubgraph.verts:= by exact fun a ↦ h5 a
    aesop
  have h4: y ∈ p.toSubgraph.support ↔ ∃ w, p.toSubgraph.Adj y w:=by exact SimpleGraph.Subgraph.mem_support p.toSubgraph
  have h5: y ∉ p.toSubgraph.support → ¬∃ w, p.toSubgraph.Adj y w:= by aesop
  have h6: ¬∃ w, p.toSubgraph.Adj y w:= by aesop
  have h7: ∀w, ¬ p.toSubgraph.Adj y w:= by aesop
  have h8: ¬ p.toSubgraph.Adj y x:= by aesop
  have h8: ¬ p.toSubgraph.Adj x y:= by exact fun a ↦ h7 x (id (SimpleGraph.Subgraph.adj_symm p.toSubgraph a))
  exact h8

lemma InPathNotEndpointinMatching {M: G.Subgraph}{p: G.Walk u v}
(h1: p.IsAugmentingPath M) (h2: ¬ (x=u ∨ x = v))(h3: x ∈ p.support): x ∈ M.verts:= by
  have h4: ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y):= by
    exact h1.alternates
  simp_all only [not_or, ne_eq]
  obtain ⟨h2l, h2r⟩ := h2
  have h5: u ≠ v:= by exact h1.ends_unsaturated.left
  have h6: ∃w, s(w,x) ∈ p.edges:= by sorry
  sorry





lemma PathVertexAdjMatchingThenPath {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M)(h3:x ∈ p.support):
∀z, M.Adj x z → p.toSubgraph.Adj x z:= by
  intro z h4
  have h5: x ∈ M.verts:= by exact M.edge_vert h4
  have h6: ∃w, M.Adj x w ∧ ∀y, M.Adj x y → y = w:= by aesop
  have h7: M.Adj x z ∧ ∀ y, M.Adj x y → y = z:= by aesop
  have h8: ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y):= by exact h2.alternates
  have h8: ∀ w: V, w ≠ z → s(w,x) ∈ p.edges → s(x,z) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x z):= by
    revert x z
    exact fun {x} h3 z h4 h5 h6 h7 w a a_1 a_2 ↦ h8 a a_1 a_2

  show s(x,z) ∈ p.toSubgraph.edgeSet
  by_contra h9
  have h9: s(x,z) ∉ p.edges:=by aesop
  have h10: ∃w, w ≠ z:= by
    use x
    exact SimpleGraph.Subgraph.Adj.ne h4
  sorry








lemma AugPathMatchingNoNeighbours {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M):
∀x y : V, x ∈ p.support → y ∉ p.support →
  ¬ (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj x y
:= by
intro x y h3 h4
have h10: ¬p.toSubgraph.Adj x y := by exact PathNotConnectedToOutsideOfPath h4
have h11: ¬p.toSubgraph.spanningCoe.Adj x y := by exact h10
by_cases h5: (x=u ∨ x = v)
· have h8: ¬M.Adj x y:= by exact EndsNotConnectedToMatching h2 h5
  have h9: ¬M.spanningCoe.Adj x y := by exact h8
  unfold symmDiff
  intro a
  cases a with
  |inl a => aesop
  |inr a => aesop
· unfold symmDiff
  intro a
  cases a with
  |inl a =>
    have h8: ∀z, M.Adj x z → p.toSubgraph.Adj x z:= by exact fun z a ↦ PathVertexAdjMatchingThenPath h1 h2 h3 z a
    simp_all


  |inr a =>
    simp_all



--- Lemma for Lauren's node above mine
lemma AugPathUniqueNeighbourInAugPath {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M) :
∀w : V, w∈p.support → ∃! w',(symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj w w' := by
intro w hp
have h3: ∀x y : V, x ∈ p.support → y ∉ p.support → ¬ (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj x y:= by
  exact fun x y a a_1 ↦ AugPathMatchingNoNeighbours h1 h2 x y a a_1
have h3: ∀y:V, y ∉ p.support → ¬ (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj w y := by
  aesop
sorry
