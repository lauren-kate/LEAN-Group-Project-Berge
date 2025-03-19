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

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.Group.Even


namespace SimpleGraph

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {F : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w x : V}


namespace Walk

structure IsAlternatingCycle (p : F.Walk u u) (M : G.Subgraph) extends p.IsCycle : Prop where
  alternates : ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y)

structure IsAlternatingPath (p : F.Walk u v) (M : G.Subgraph) extends p.IsPath : Prop where
  alternates : ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y)

structure IsAugmentingPath (p : F.Walk u v) (M : G.Subgraph) extends p.IsAlternatingPath M : Prop where
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
def Adj (c : F.ConnectedComponent) (u v : V) : Prop :=
  u ∈ c.supp ∧ v ∈ c.supp ∧ F.Adj u v


theorem component_adj_symm (c : F.ConnectedComponent) : Symmetric c.Adj := by
  intros x y h
  obtain ⟨ h_xc, h_yc, h_f ⟩ := h
  exact ⟨ h_yc, h_xc , F.adj_symm h_f ⟩


def edgeSet (c : F.ConnectedComponent) : Set (Sym2 V) :=
  Sym2.fromRel c.component_adj_symm


end ConnectedComponent

namespace Walk

def vertexSet (p : F.Walk u v) : Set V :=
  {v : V | v ∈ p.support}

def edgeSet (p : F.Walk u v) : Set (Sym2 V) :=
  {e : Sym2 V | e ∈ p.edges}

end Walk

namespace Walk

structure IsAltCycleComponent (p : F.Walk u u) (M : G.Subgraph) (c : F.ConnectedComponent) extends p.IsAlternatingCycle M : Prop where
  vertices_eq : c.supp = p.vertexSet
  edges_eq : c.edgeSet = p.edgeSet


structure IsAltPathComponent (p : F.Walk u v) (M : G.Subgraph) (c : F.ConnectedComponent) extends p.IsAlternatingPath M : Prop where
  vertices_eq : c.supp = p.vertexSet
  edges_eq : c.edgeSet = p.edgeSet


end Walk

namespace ConnectedComponent

-- whether a component is equivalent to a alternating path or cycle
def componentAltCycle (c : F.ConnectedComponent) (M : G.Subgraph) : Prop :=
  ∃ (u : V) (p : F.Walk u u), p.IsAltCycleComponent M c


def componentAltPath (c : F.ConnectedComponent) (M : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : F.Walk u v), p.IsAltPathComponent M c

end ConnectedComponent



theorem cycle_is_even(M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∀ (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u u ), p.IsCycle → Even p.edgeSet.encard := by
  let F := (symmDiff M.spanningCoe M'.spanningCoe)
  sorry

theorem component_is_alt (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∀(cc : (symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent), (cc.componentAltPath M) ∨ (cc.componentAltCycle M):=
  sorry

theorem cycle_eq_in_symm_diff(M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∀ (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u u ), p.IsCycle → (p.edgeSet ∩ M.edgeSet).ncard = (p.edgeSet ∩ M'.edgeSet).ncard := by
  let F := (symmDiff M.spanningCoe M'.spanningCoe)
  sorry

theorem component_edges_greater_than (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching) (he: M'.edgeSet.ncard > M.edgeSet.ncard):
∃ (cc: (symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent), (cc.componentAltPath M) ∧ ((cc.edgeSet ∩ M'.edgeSet).ncard > (cc.edgeSet ∩ M.edgeSet).ncard):=
  sorry

theorem exists_aug_path (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∃ (p: (symmDiff M.spanningCoe M'.spanningCoe).Walk u v), (p.IsAugmentingPath M):=
sorry

theorem berge_left (M : G.Subgraph): IsMaximumMatching M → ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M :=
  sorry
