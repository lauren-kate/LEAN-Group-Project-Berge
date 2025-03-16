import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph


import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.SymmDiff

import LEANGroupProjectBerge.Basic
import LEANGroupProjectBerge.AugmentingEdges


namespace SimpleGraph

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w x: V}

open Walk

lemma mem_support_contr_simple (x:V) (G : SimpleGraph V) :  x ∉ G.support ↔ ¬ ∃ (w : V), G.Adj x w := by rfl

lemma mem_support_contr (x:V) (H : G.Subgraph) :  x ∉ H.support ↔ ¬ ∃ (w : V), H.Adj x w := by rfl


lemma not_adj_gen (x w:V) (H:G.Subgraph)(h: x ∉ H.support):  ¬H.Adj x w :=
  have h1: ¬∃ (w : V), H.Adj x w := Iff.mp (mem_support_contr x H) h
  have h2: ∀ (w:V), ¬H.Adj x w := by aesop--exact h1
  show ¬H.Adj x w from h2 w


--mem_symDiff_edgeSet_graphs
lemma mem_symDiff_edgeSet_graphs (x y:V) (H J:G.Subgraph) (S: SimpleGraph V) (h1: S = symmDiff H.spanningCoe J.spanningCoe) : s(x,y) ∈ S.edgeSet ↔ s(x,y) ∈ H.spanningCoe.edgeSet ∧ s(x,y) ∉ J.spanningCoe.edgeSet ∨ s(x,y) ∈ J.spanningCoe.edgeSet ∧ s(x,y) ∉ H.spanningCoe.edgeSet :=
  by aesop

--mpr_not_mem_symDiff_edgeSet_graphs
lemma mpr_not_mem_symDiff_edgeSet_graphs (x y:V) (H J:G.Subgraph) (S: SimpleGraph V) (h1: S = symmDiff H.spanningCoe J.spanningCoe) (h2: (s(x,y) ∉ H.spanningCoe.edgeSet ∧ s(x,y) ∉ J.spanningCoe.edgeSet)):  s(x,y)∉S.edgeSet :=
  have h5: ¬(s(x,y) ∈ H.spanningCoe.edgeSet ∧ s(x,y) ∉ J.spanningCoe.edgeSet ∨ s(x,y) ∈ J.spanningCoe.edgeSet ∧ s(x,y) ∉ H.spanningCoe.edgeSet) := by aesop
  have h6: s(x,y)∉S.edgeSet := Iff.mpr (Iff.not (mem_symDiff_edgeSet_graphs x y H J S h1)) h5
  show s(x,y)∉S.edgeSet from h6




open Classical

--Unused assumptions: [Finite V] (h1:M.IsMatching) (h2: p.IsAugmentingPath M) (h5: y ∉ p.toSubgraph.support)
lemma outside_path (M :G.Subgraph) (M':SimpleGraph V) (u v x y:V) (p : G.Walk u v) (h3 : M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)) (h4:x ∉ p.toSubgraph.support)  : (¬M.Adj x y ↔ ¬M'.Adj x y) where
    mp :=
      fun h: ¬M.Adj x y =>
      have h7 : s(x, y) ∉ M.spanningCoe.edgeSet := Iff.mpr (Iff.not (M.spanningCoe.mem_edgeSet)) h
      have h8 : s(x,y) ∉ p.toSubgraph.spanningCoe.edgeSet := Iff.mpr (Iff.not (p.toSubgraph.spanningCoe.mem_edgeSet)) ((not_adj_gen x y p.toSubgraph) h4)
      have h9: s(x, y) ∉ M.spanningCoe.edgeSet ∧ s(x,y) ∉ p.toSubgraph.spanningCoe.edgeSet := And.intro h7 h8
      have h10 : s(x,y) ∉ M'.edgeSet := (mpr_not_mem_symDiff_edgeSet_graphs x y M p.toSubgraph M') h3 h9
      have h11: ¬M'.Adj x y := Iff.mp (Iff.not (M'.mem_edgeSet)) h10
      show ¬M'.Adj x y from h11


    mpr :=
      fun h: ¬M'.Adj x y =>
      have h7: s(x, y) ∉ M'.edgeSet := Iff.mpr (Iff.not (M'.mem_edgeSet)) h
      have h8 : s(x,y) ∉ p.toSubgraph.spanningCoe.edgeSet := Iff.mpr (Iff.not (p.toSubgraph.spanningCoe.mem_edgeSet)) ((not_adj_gen x y p.toSubgraph) h4)
      have h9: ¬M.Adj x y :=
        byContradiction
          (fun contr: ¬¬M.Adj x y =>
          have h10: M.Adj x y := of_not_not contr
          have h11: s(x, y) ∈  M.spanningCoe.edgeSet := Iff.mpr (M.mem_edgeSet) h10
          have h12: s(x, y) ∈  M.spanningCoe.edgeSet ∧ s(x,y) ∉ p.toSubgraph.spanningCoe.edgeSet := And.intro h11 h8
          have h13: s(x, y) ∈  M.spanningCoe.edgeSet ∧ s(x,y) ∉ p.toSubgraph.spanningCoe.edgeSet ∨ s(x, y) ∈ p.toSubgraph.spanningCoe.edgeSet ∧ s(x,y) ∉ M.spanningCoe.edgeSet := Or.intro_left (s(x, y) ∈ p.toSubgraph.spanningCoe.edgeSet ∧ s(x,y) ∉ M.spanningCoe.edgeSet) h12
          have h20: s(x, y) ∈  M'.edgeSet := Iff.mpr (mem_symDiff_edgeSet_graphs x y M p.toSubgraph M' h3) h13
          show False from h7 h20)
      show ¬M.Adj x y from h9


lemma iff_not_opposite {a b : Prop} (h : ¬a ↔ ¬b): a ↔ b := by aesop


lemma outside_path_forall (M :G.Subgraph) (M':SimpleGraph V) (u v:V) (p : G.Walk u v) (h3 : M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)) : ∀ x y : V,  (x ∉ p.toSubgraph.support → (M.Adj x y ↔ M'.Adj x y)) := by
  intro x y
  intro h
  exact iff_not_opposite (outside_path M M' u v x y p h3 h)
