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


namespace Walk

structure IsAlternatingCycle {F : SimpleGraph V} {u : V} (p : F.Walk u u) (M : G.Subgraph) extends p.IsCycle : Prop where
  alternates : ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y)

structure IsAlternatingPath {F : SimpleGraph V} {u v : V} (p : F.Walk u v) (M : G.Subgraph) extends p.IsPath : Prop where
  alternates : ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y)

structure IsAugmentingPath {F : SimpleGraph V} {u v : V} (p : F.Walk u v) (M : G.Subgraph) extends p.IsAlternatingPath M : Prop where
  ends_unsaturated : u≠v ∧ u ∉ M.support ∧ v ∉ M.support

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



namespace walk

theorem BergesTheorem (M : G.Subgraph): IsMaximumMatching M ↔ ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M :=
  sorry

end walk


namespace Subgraph

--Use this to delete unsaturated vertices to get IsMatching for a subgraph
def saturatedSubgraph (M : G.Subgraph) : G.Subgraph where
  verts := M.support;
  Adj := M.Adj;
  adj_sub := M.adj_sub;
  edge_vert := fun h => M.mem_support.mpr ⟨_, h⟩ ;
  symm := M.symm;

end Subgraph




namespace ConnectedComponent


-- adjacency and edge set of connected components
def Adj {F : SimpleGraph V} (c : F.ConnectedComponent) (u v : V) : Prop :=
  u ∈ c.supp ∧ v ∈ c.supp ∧ F.Adj u v


theorem component_adj_symm {F : SimpleGraph V} (c : F.ConnectedComponent) : Symmetric c.Adj := by
  intros x y h
  obtain ⟨ h_xc, h_yc, h_f ⟩ := h
  exact ⟨ h_yc, h_xc , F.adj_symm h_f⟩


def edgeSet {F : SimpleGraph V} (c : F.ConnectedComponent) : Set (Sym2 V) :=
  Sym2.fromRel c.component_adj_symm



-- whether a component is equivalent to a alternating path or cycle
def componentAltCycle {F : SimpleGraph V} (c : F.ConnectedComponent) (M : G.Subgraph) : Prop :=
  ∃ (u : V) (p : F.Walk u u), p.IsAlternatingCycle M ∧
   ∀x: V, x ∈ c.supp ↔ x ∈ p.support ∧
   ∀e: Sym2 V, e ∈ c.edgeSet ↔ e ∈ p.edges


def componentAltPath {F : SimpleGraph V} (c : F.ConnectedComponent) (M : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : F.Walk u v), p.IsAlternatingPath M ∧
   ∀x: V, x ∈ c.supp ↔ x ∈ p.support ∧
   ∀e: Sym2 V, e ∈ c.edgeSet ↔ e ∈ p.edges



-- useful lemmas
theorem walk_vertex_supp {F : SimpleGraph V} {u v w : V} (c : F.ConnectedComponent) (p : F.Walk u v) :
  F.connectedComponentMk u = c → w ∈ p.support → w ∈ c.supp := by
  sorry


theorem walk_edge_supp {F : SimpleGraph V} {u v: V} (c : F.ConnectedComponent) (p : F.Walk u v) (e : Sym2 V) :
  F.connectedComponentMk u = c → e ∈ p.edges → e ∈ c.edgeSet := by
  sorry


end ConnectedComponent
