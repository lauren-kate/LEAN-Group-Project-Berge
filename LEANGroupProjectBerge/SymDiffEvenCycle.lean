/-
Copyright (c) 2025 Oscar Bryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oscar Bryan, Reuben Brown, Spraeha Jha, A. Basak Kaya, Joshua Render, Lauren Kate Thompson
-/
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
