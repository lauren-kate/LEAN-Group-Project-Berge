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
variable {u v w x y: V}



open Walk

--IsMatching for simple graphs (For my own ease of use)
def IsMatchingSimple (G:SimpleGraph V): Prop :=
  ∀ v : V, v ∈ G.support → ∃! w, G.Adj v w


--Contrapositive for SimpleFraph.Subgraph.mem_support (For my own ease of use)
lemma mem_support_contr (x:V) (H : G.Subgraph) :  x ∉ H.support ↔ ¬ ∃ (w : V), H.Adj x w := by rfl


lemma not_adj_gen (x w:V) (H:G.Subgraph)(h: x ∉ H.support):  ¬H.Adj x w :=
  have h1: ¬∃ (w : V), H.Adj x w := Iff.mp (mem_support_contr x H) h
  have h2: ∀ (w:V), ¬H.Adj x w := by aesop
  show ¬H.Adj x w from h2 w


--Rewrite of Set.mem_symmDiff for edgesets of graphs
lemma mem_symDiff_edgeSet_graphs (x y:V) (H J:G.Subgraph) (S: SimpleGraph V) (h1: S = symmDiff H.spanningCoe J.spanningCoe) : s(x,y) ∈ S.edgeSet ↔ s(x,y) ∈ H.spanningCoe.edgeSet ∧ s(x,y) ∉ J.spanningCoe.edgeSet ∨ s(x,y) ∈ J.spanningCoe.edgeSet ∧ s(x,y) ∉ H.spanningCoe.edgeSet :=
  by aesop

lemma mpr_not_mem_symDiff_edgeSet_graphs (x y:V) (H J:G.Subgraph) (S: SimpleGraph V) (h1: S = symmDiff H.spanningCoe J.spanningCoe) (h2: (s(x,y) ∉ H.spanningCoe.edgeSet ∧ s(x,y) ∉ J.spanningCoe.edgeSet)):  s(x,y)∉S.edgeSet :=
  have h5: ¬(s(x,y) ∈ H.spanningCoe.edgeSet ∧ s(x,y) ∉ J.spanningCoe.edgeSet ∨ s(x,y) ∈ J.spanningCoe.edgeSet ∧ s(x,y) ∉ H.spanningCoe.edgeSet) := by aesop
  have h6: s(x,y)∉S.edgeSet := Iff.mpr (Iff.not (mem_symDiff_edgeSet_graphs x y H J S h1)) h5
  show s(x,y)∉S.edgeSet from h6




open Classical


lemma outside_path [Finite V] (M :G.Subgraph) (M':SimpleGraph V) (u v x y:V) (p : G.Walk u v) (h3 : M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)) (h4:x ∉ p.toSubgraph.support)  : (¬M.Adj x y ↔ ¬M'.Adj x y) where
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


lemma outside_path_forall [Finite V] (M :G.Subgraph) (M':SimpleGraph V) (u v:V) (p : G.Walk u v) (h3 : M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)) : ∀ x y : V,  (x ∉ p.toSubgraph.support → (M.Adj x y ↔ M'.Adj x y)) := by
  intro x y
  intro h
  exact iff_not_opposite (outside_path M M' u v x y p h3 h)




lemma x_nin_p [Finite V] (M :G.Subgraph) (M':SimpleGraph V) (u v x:V) (p : G.Walk u v) (h3 : M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)): x ∈ (M'.support \ p.toSubgraph.support) → x ∉ p.toSubgraph.support := by aesop


lemma unique_adj_in_m_m' [Finite V] (M :G.Subgraph) (M':SimpleGraph V)  :∀ x :V, ((∀ y : V, M.Adj x y ↔ M'.Adj x y) → ((∃! y:V, M.Adj x y)↔(∃! y:V, M'.Adj x y))) := by
  intro x
  exact
    fun h4:(∀ y : V, M.Adj x y ↔ M'.Adj x y) =>
    have h5: (∃! y:V, M.Adj x y)↔(∃! y:V, M'.Adj x y) := existsUnique_congr h4
    h5


lemma x_in_path_or_not [Finite V] (M : G.Subgraph) (M': SimpleGraph V) (u v x: V ) (p: G.Walk u v) (h3: M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)): x ∈ M'.support →  (x ∈ p.toSubgraph.support ∨ x ∈ (M'.support \ p.toSubgraph.support)) := by
  intro h
  exact
    have h5: x ∈ p.toSubgraph.support ∨ ¬x ∈ p.toSubgraph.support := or_not
    have h6: ¬x ∈ p.toSubgraph.support → x ∈ (M'.support \ p.toSubgraph.support) := by aesop
    have h7: x ∈ p.toSubgraph.support ∨ x ∈ (M'.support \ p.toSubgraph.support) := by aesop
    h7


lemma xy_in_m'_x_in_m_or_p_hl [Finite V] (M :G.Subgraph) (M':SimpleGraph V) (u v x y:V) (p : G.Walk u v) (h3 : M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)) (h4:s(x,y) ∈ M'.edgeSet) (hl: s(x,y) ∈ M.spanningCoe.edgeSet): x ∈ M.spanningCoe.support ∨ x ∈ p.toSubgraph.spanningCoe.support :=
  have h5: M.spanningCoe.Adj x y := by aesop
  have h6: ∃ w:V, M.spanningCoe.Adj x w := by aesop
  have h8: x ∈ M.spanningCoe.support ↔ ∃ w:V, M.spanningCoe.Adj x w := Iff.rfl
  have h7: x ∈ M.spanningCoe.support := Iff.mpr h8 h6
  have h8: x ∈ M.spanningCoe.support ∨ x ∈ p.toSubgraph.spanningCoe.support := by aesop
  h8

lemma xy_in_m'_x_in_m_or_p_hr [Finite V] (M :G.Subgraph) (M':SimpleGraph V) (u v x y:V) (p : G.Walk u v) (h3 : M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)) (h4:s(x,y) ∈ M'.edgeSet) (hr: s(x,y) ∈ p.toSubgraph.spanningCoe.edgeSet): x ∈ M.spanningCoe.support ∨ x ∈ p.toSubgraph.spanningCoe.support :=
  have h5: p.toSubgraph.spanningCoe.Adj x y := by aesop
  have h6: ∃ w:V, p.toSubgraph.spanningCoe.Adj x w := by aesop
  have h8: x ∈ p.toSubgraph.spanningCoe.support ↔ ∃ w:V, p.toSubgraph.spanningCoe.Adj x w := Iff.rfl
  have h7: x ∈ p.toSubgraph.spanningCoe.support := Iff.mpr h8 h6
  have h8: x ∈ M.spanningCoe.support ∨ x ∈ p.toSubgraph.spanningCoe.support := by aesop
  h8

lemma xy_in_m'_x_in_m_or_p [Finite V] (M :G.Subgraph) (M':SimpleGraph V) (u v x y:V) (p : G.Walk u v) (h3 : M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)) (h4:s(x,y) ∈ M'.edgeSet): x ∈ M'.support → (x ∈ M.spanningCoe.support ∨ x ∈ p.toSubgraph.spanningCoe.support) :=
  fun h5: x ∈ M'.support =>
  have h6: s(x,y) ∈ symmDiff M.spanningCoe.edgeSet p.toSubgraph.spanningCoe.edgeSet := by aesop
  have h8: s(x,y) ∈ M.spanningCoe.edgeSet ∧ s(x,y) ∉ p.toSubgraph.spanningCoe.edgeSet ∨ s(x,y) ∈ p.toSubgraph.spanningCoe.edgeSet ∧ s(x,y) ∉ M.spanningCoe.edgeSet  := Iff.mp (mem_symDiff_edgeSet_graphs x y M p.toSubgraph M' h3) h4
  have h9: s(x,y) ∈ M.spanningCoe.edgeSet ∨ s(x,y) ∈ p.toSubgraph.spanningCoe.edgeSet := by aesop
  show x ∈ M.spanningCoe.support ∨ x ∈ p.toSubgraph.spanningCoe.support by
    cases h9 with
    | inl hl => exact xy_in_m'_x_in_m_or_p_hl M M' u v x y p h3 h4 hl
    | inr hr => exact xy_in_m'_x_in_m_or_p_hr M M' u v x y p h3 h4 hr

lemma x_in_m_or_p [Finite V] (M :G.Subgraph) (M':SimpleGraph V) (u v:V) (p : G.Walk u v) (h3 : M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)): x ∈ M'.support → (x ∈ M.spanningCoe.support ∨ x ∈ p.toSubgraph.spanningCoe.support):=
  fun h4: x ∈ M'.support =>
  have h5: ∃ y:V, s(x,y) ∈ M'.edgeSet := by aesop
  Exists.elim h5
    (fun y =>
    fun h6: s(x,y) ∈ M'.edgeSet =>
    have h7: x ∈ M.spanningCoe.support ∨ x ∈ p.toSubgraph.spanningCoe.support :=
      (xy_in_m'_x_in_m_or_p M M' u v x y p h3 h6) h4
    h7
    )


lemma x_in_m_not_p [Finite V] (M :G.Subgraph) (u v:V) (p : G.Walk u v) (h4: x ∉ p.toSubgraph.spanningCoe.support): x ∈ M.spanningCoe.support ∨ x ∈ p.toSubgraph.spanningCoe.support → x ∈ M.spanningCoe.support := by aesop


lemma outside_path_unique_neighbour [Finite V] (M :G.Subgraph) (M':SimpleGraph V) (u v:V) (p : G.Walk u v) (h1:M.IsMatching) (h3 : M' = (symmDiff M.spanningCoe p.toSubgraph.spanningCoe))  : ∀ x : V,  (x ∈ (M'.support \ p.toSubgraph.support) → (∃! y:V, M'.Adj x y)) :=by
  intro x
  exact
    fun h4: x ∈ (M'.support \ p.toSubgraph.support) =>
    have h5: x ∉ p.toSubgraph.spanningCoe.support := x_nin_p M M' u v x p h3 h4
    have h6: ∀ y:V, M.Adj x y ↔ M'.Adj x y := by
      intro y
      exact iff_not_opposite (outside_path M M' u v x y p h3 h5)
    have h7: (∃! y:V, M.Adj x y)↔(∃! y:V, M'.Adj x y) := (unique_adj_in_m_m' M M') x h6
    have h10: x ∈ M'.support := by aesop
    have h11: x ∈ M.spanningCoe.support ∨ x ∈ p.toSubgraph.spanningCoe.support :=  ((x_in_m_or_p M M' u v p h3) h10)
    have h12: x ∈ M.spanningCoe.support := x_in_m_not_p M u v p h5 h11
    have h13: x ∈ M.support := by aesop
    have h14: M.support = M.verts := Subgraph.IsMatching.support_eq_verts h1
    have h15: x ∈ M.verts := by aesop
    have h8: ∃! y:V, M.Adj x y := by exact h1 (h15)
    have h9: (∃! y:V, M'.Adj x y) := Iff.mp h7 h8
    h9
