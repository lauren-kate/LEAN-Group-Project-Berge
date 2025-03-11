import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import LEANGroupProjectBerge.Basic



namespace SimpleGraph

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w x: V}

open Walk

lemma memSupportContr (x:V) (H : G.Subgraph) :  x ∉ H.support ↔ ¬ ∃ (w : V), H.Adj x w := by rfl


lemma notAdjGen (x w:V) (H:G.Subgraph)(h: x ∉ H.support):  ¬H.Adj x w :=
  have h1: ¬∃ (w : V), H.Adj x w := Iff.mp (memSupportContr x H) h
  have h2: ∀ (w:V), ¬H.Adj x w := by aesop--exact h1
  show ¬H.Adj x w from h2 w


lemma notAdjInP (M M':G.Subgraph) (u v w x:V) (p : G.Walk u v) (h1:M.IsMatching) (h2: p.IsAugmenting M) (h3 : M' = (symmDiff M p.toSubgraph)) (h4: w ∉ p.toSubgraph.support) (h5: x ∉ p.toSubgraph.support): ¬p.toSubgraph.Adj w x :=
  (notAdjGen w x p.toSubgraph) h4


lemma outsidePath2 [Finite V] (M M':G.Subgraph) (u v x y:V) (p : G.Walk u v) (h1:M.IsMatching) (h2: p.IsAugmenting M) (h3 : M' = (symmDiff M p.toSubgraph)) (h4:x ∉ p.toSubgraph.verts) (h5: y ∉ p.toSubgraph.verts) : (¬M.Adj x y ↔ ¬M'.Adj x y)where
    mp := sorry
    mpr := sorry
