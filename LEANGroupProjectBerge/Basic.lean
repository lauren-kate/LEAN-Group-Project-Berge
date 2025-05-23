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



def vertexSet (p : F.Walk u v) : Set V :=
  {v : V | v ∈ p.support}

def edgeSet (p : F.Walk u v) : Set (Sym2 V) :=
  {e : Sym2 V | e ∈ p.edges}


theorem edgeSet_toSubgraph_eq (p : F.Walk u v) : p.edgeSet = p.toSubgraph.edgeSet :=
  Eq.symm p.edgeSet_toSubgraph


end Walk



namespace Subgraph


-- i think we can get rid of this
-- as a subtype
def augPath (M : G.Subgraph) (u v : V) : Type u :=
  {w : G.Walk u v // w.IsAugmentingPath M}



--Added maximal matching for completeness' sake with maximum matchings - we dont need for Berge's
def IsMaximalMatching (M : G.Subgraph): Prop :=
  M.IsMatching ∧
  (¬∃ v w, v ∉ M.support ∧ w ∉ M.support ∧ G.Adj v w)

def IsMaximumMatching (M : G.Subgraph): Prop :=
  M.IsMatching
  ∧ (¬∃ N : G.Subgraph, N.IsMatching ∧ M.edgeSet.encard < N.edgeSet.encard)





--Use this to delete unsaturated vertices to get IsMatching for a subgraph
def saturatedSubgraph (H : SimpleGraph V) (h_sub : H ≤ G) : G.Subgraph where
  verts := H.support;
  Adj := H.Adj;
  adj_sub := @h_sub
  edge_vert := fun h => ⟨_, h⟩
  symm := H.symm;


end Subgraph

-- To use saturatedSubgraph with M Δ P
theorem subg_path_symdiff_subg {u v : V} (p : G.Walk u v) (M : G.Subgraph) :
    symmDiff M.spanningCoe p.toSubgraph.spanningCoe ≤ G := by
  intro x y h
  cases h with
  | inl h =>
    apply M.adj_sub; aesop
  | inr h =>
    show s(x,y) ∈ G.edgeSet; apply p.edges_subset_edgeSet
    have : s(x,y) ∈ p.toSubgraph.edgeSet := h.1
    aesop





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






-- useful theorems for handling matchings, walks and components with the above definitions
variable {M₁ : G.Subgraph}
variable {M₂ : G.Subgraph}


-- use to generate contradictions with matchings
lemma matching_contr (hm : M₁.IsMatching) {a b c : V} (hne : a≠b) (h : M₁.Adj c a) (h' : M₁.Adj c b) : False := by
  match hm (M₁.edge_vert h) with
  | ⟨ x, h_x ⟩ =>
    have : a=x := h_x.2 a h
    have : b=x := h_x.2 b h'
    exact hne (by aesop)


lemma alt_of_cons {u v w : V} {F : SimpleGraph V} {h : F.Adj u v} {p : F.Walk v w} :
    (Walk.cons h p).IsAlternatingPath M → p.IsAlternatingPath M := by
  intro h_alt
  constructor
  · exact h_alt.of_cons
  · intros x y z h_xnez h_xy h_yz
    let p' := Walk.cons h p
    have h_xyp' : s(x,y) ∈ p'.edges := by aesop
    have h_yzp' : s(y,z) ∈ p'.edges := by aesop
    exact h_alt.alternates h_xnez h_xyp' h_yzp'


namespace Walk

theorem NotpSupportNotEdge(p:G.Walk u v):
w ∉ p.support →  ∀x,s(x,w) ∉ p.edges:= by
  intro h1 x h2
  have h3: s(x,w) ∈ p.edgeSet:= by exact h2
  have h4: s(x,w) ∈ p.toSubgraph.edgeSet:=by exact (mem_edges_toSubgraph p).mpr h2
  have h5: w ∈ p.toSubgraph.support:= by
    refine (Subgraph.mem_support p.toSubgraph).mpr ?_
    use x
    exact Subgraph.adj_symm p.toSubgraph h4
  have h6: w ∈ p.support:= by exact snd_mem_support_of_mem_edges p h2
  contradiction


lemma AdjImpInEdgeSet{G: SimpleGraph V}: G.Adj x w ↔ s(x,w) ∈ G.edgeSet:=by
  exact Eq.to_iff rfl

lemma InPathSubgraphIffInPath{p: G.Walk u v}: s(x,w) ∈ p.toSubgraph.edgeSet ↔ s(x,w) ∈ p.edgeSet:= by
  apply Iff.intro
  · aesop
  · aesop



-- if two walks have the same list of vertices, they have the same vertex set
theorem supp_vertexset_eq (p : G.Walk u v) (q : F.Walk u v) : p.support=q.support → p.vertexSet=q.vertexSet := by
  intro h
  unfold vertexSet
  rw[h]


-- transferring a walk to another graph maintains the vertex set
theorem transfer_vertexset_eq (p : G.Walk u v) (h : ∀e ∈ p.edges, e ∈ F.edgeSet) :
  p.vertexSet = (p.transfer F h).vertexSet := by
  apply supp_vertexset_eq
  exact Eq.symm (support_transfer p h)


-- the vertex set of the concatenation of an edge with a walk is the old walk's vertex set U the new vertex
theorem cons_vertexset (p : G.Walk w x) (h_adj : G.Adj v w) : (Walk.cons h_adj p).vertexSet = p.vertexSet ∪ {v} := by
  apply Set.ext; intro a
  apply Iff.intro
  · intro h_a
    have : a=v ∨ a ∈ p.support := List.mem_cons.mp h_a
    cases this <;> aesop
  · intro h_a
    apply List.mem_cons.mpr
    aesop


-- a walk has the same vertex set as its reverse
theorem reverse_vertexset_eq (p : G.Walk u v) : p.vertexSet = p.reverse.vertexSet := by
  apply Set.ext; intro x
  unfold vertexSet
  rw[support_reverse]
  exact List.mem_reverse.symm


-- if two walks have the same list of edges, they have the same edgeset
theorem edges_edgeset_eq (p : G.Walk u v) (q : F.Walk u v) : p.edges=q.edges → p.edgeSet=q.edgeSet := by
  intro h
  unfold edgeSet
  rw[h]


-- transferring a walk to another graph maintains the edge set
theorem transfer_edgeset_eq (p : G.Walk u v) (h : ∀e ∈ p.edges, e ∈ F.edgeSet) :
  p.edgeSet = (p.transfer F h).edgeSet := by
  apply edges_edgeset_eq
  exact Eq.symm (edges_transfer p h)


-- the edgeset of the concatenation of an edge with a walk is the old walk's edgeset U the edge
theorem cons_edgeset (p : G.Walk w x) (h_adj : G.Adj v w) : (Walk.cons h_adj p).edgeSet = p.edgeSet ∪ {s(v,w)} := by
  apply Set.ext; apply Sym2.ind; intro a b
  apply Iff.intro
  · intro h_ab
    replace h_ab : s(a,b)= s(v,w) ∨ s(a,b) ∈ p.edges := List.mem_cons.mp h_ab
    cases h_ab <;> aesop
  · intro h_ab
    show s(a,b) ∈ s(v,w) :: p.edges
    apply List.mem_cons.mpr
    cases h_ab <;> aesop

-- a walk has the same edge set as its reverse
theorem reverse_edgeset_eq (p : G.Walk u v) : p.edgeSet = p.reverse.edgeSet := by
  apply Set.ext; intro x
  unfold edgeSet
  rw[edges_reverse]
  exact List.mem_reverse.symm

-- can be used to provide a walk between an intermediary vertex and the end vertex
theorem support_vertex_walk (p : F.Walk u v) : w ∈ p.support → Nonempty (F.Walk w v) := by
  induction p with
  | nil =>
    intro h
    rename_i u
    have : w=u :=by aesop
    rw [this]
    exact Nonempty.intro Walk.nil
  | cons h_adj q ih =>
    rename_i u w' v
    if h : w=u then
      subst h
      exact fun _ => Nonempty.intro (Walk.cons h_adj q)
    else
      intro a
      simp_all only [Walk.support_cons, List.mem_cons, false_or]


-- any walk in the symmetric difference of two matchings satisfies the alternating condition
theorem match_symmdiff_walk_alt (h_m₁ : M₁.IsMatching) (h_m₂ : M₂.IsMatching) {u v : V} (p : (symmDiff M₁.spanningCoe M₂.spanningCoe).Walk u v) :
    ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M₁.Adj w x ↔ ¬M₁.Adj x y) := by
  let F := symmDiff M₁.spanningCoe M₂.spanningCoe
  intro w x y h_wy_ne h_p_wx h_p_xy
  constructor
  · exact fun h h' => matching_contr h_m₁ h_wy_ne h.symm h'
  · intro h_nadj_xy
    have h_fwx : F.Adj w x := p.adj_of_mem_edges h_p_wx
    have h_fxy : F.Adj x y := p.adj_of_mem_edges h_p_xy
    have h_m₂xy : M₂.Adj x y := by cases h_fxy <;> aesop
    cases h_fwx with
    | inl h => exact h.1
    | inr h => exact False.elim <| matching_contr h_m₂ h_wy_ne h.1.symm h_m₂xy


theorem ReverseAlternatingPathAlternating{M:G.Subgraph}{p: G.Walk u v}
(h1: p.IsAlternatingPath M ):
p.reverse.IsAlternatingPath M:= by
  constructor
  · have h2: p.IsPath:= by exact h1.toIsPath
    exact (isPath_reverse_iff p).mpr h2
  · intro w x y
    simp
    revert y x w
    exact h1.alternates


theorem ReverseAugmentingPathAugmenting{M:G.Subgraph}{p: G.Walk u v}
(h1: p.IsAugmentingPath M ):
p.reverse.IsAugmentingPath M:= by
  constructor
  · refine ReverseAlternatingPathAlternating ?_
    exact h1.toIsAlternatingPath
  · apply And.intro
    · have h2: u≠v:= by exact h1.ends_unsaturated.left
      aesop
    · have h2: u ∉ M.support ∧ v ∉ M.support:= by exact h1.ends_unsaturated.right
      aesop



end Walk




namespace ConnectedComponent

-- any vertex in a walk is in the same component as the end of the walk
theorem walk_vertex_supp (c : F.ConnectedComponent) (p : F.Walk u v) :
    F.connectedComponentMk v = c → w ∈ p.support → w ∈ c.supp := by
  intros h_c_eq h_wp
  subst h_c_eq
  simp_all only [mem_supp_iff, ConnectedComponent.eq]
  exact p.support_vertex_walk h_wp


-- any edge in a walk is in the edge set of the component containing the end of the walk
theorem walk_edge_supp (c : F.ConnectedComponent) (p : F.Walk u v) (e : Sym2 V) :
    F.connectedComponentMk v = c → e ∈ p.edges → e ∈ c.edgeSet := by
  revert e
  apply Sym2.ind
  intro x y h_c_eq h_ep
  show c.Adj x y
  constructor
  · have : x ∈ p.support := Walk.fst_mem_support_of_mem_edges p h_ep
    exact c.walk_vertex_supp  p h_c_eq this
  constructor
  · have : y ∈ p.support := Walk.fst_mem_support_of_mem_edges p (Sym2.eq_swap ▸ h_ep)
    exact c.walk_vertex_supp p h_c_eq this
  · exact Walk.adj_of_mem_edges p h_ep


-- if a vertex x has no neighbours, all the vertices in x's component are equal to x
theorem single_vertex (c : F.ConnectedComponent) (h : x ∈ c.supp) :
    F.neighborSet x = ∅ → ∀y : V, y ∈ c.supp → y = x := by
  intro h_nset y h_yc
  have : F.connectedComponentMk x = F.connectedComponentMk y := by aesop
  have : F.Reachable x y := ConnectedComponent.exact this
  apply Nonempty.elim this
  intro p
  cases p with
  | nil => rfl
  | cons h q =>
    rename V => z
    have h_neighbor := (F.mem_neighborSet x z).mpr h
    apply False.elim <| Set.mem_def.mp <| h_nset ▸ h_neighbor


theorem single_vertex_comp_supp (c : F.ConnectedComponent) (h : x ∈ c.supp) :
    F.neighborSet x = ∅ → c.supp = {x} := by
  intro h_nnbr
  apply Set.ext
  intro v
  apply Iff.intro
  · intro h_vc
    have : v=x := c.single_vertex h h_nnbr v h_vc
    rw[this]; trivial
  · aesop

end ConnectedComponent
