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
variable {u v w x y: V}


namespace Matching




end Matching


theorem cycle_is_even(M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∀ (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u u ), p.IsCycle → Even p.edgeSet.encard := by
  let F := (symmDiff M.spanningCoe M'.spanningCoe)
  sorry

theorem cycle_eq_in_symm_diff [Finite V] (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching) (p : F.Walk u v):
∀ (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u u ), p.IsCycle → (p.edgeSet ∩ M.edgeSet).ncard = (p.edgeSet ∩ M'.edgeSet).ncard := by
  sorry

namespace SimpleGraph
open Classical

theorem m'_iff_not_m {M': SimpleGraph V} {P: G.Walk u v} (hM': M'=(symmDiff M.spanningCoe P.toSubgraph.spanningCoe)) :
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

-- Classical
namespace Walk
namespace Path



lemma path_deg_2 (P: G.Walk u v) (hp: P.IsPath):
∀(x:V), (x ≠ u ∧ x≠ v) → (G.neighborSet x ∩ P.vertexSet).ncard = 2 := by sorry

lemma p_matched_unless_end (P: G.Walk u v) (hm : M.IsMatching) (hp: P.IsAugmentingPath M):
∀(x:V),(x ∈ P.support) ∧ (x ≠ u ∧ x≠ v) → x ∈ M.support := by
  intro x h1
  have h1a: (x ∈ P.support) := h1.left
  have h1b: (x ≠ u ∧ x≠ v) := h1.right
  have h2: P.IsPath := by exact hp.toIsPath
  have h20 : ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ P.edges → s(x,y) ∈ P.edges → (M.Adj w x ↔ ¬M.Adj x y) := hp.alternates
  have h3: (G.neighborSet x ∩ P.vertexSet).ncard = 2 := by exact path_deg_2 P h2 x h1b
  have h4: P.support.Nodup := by exact h2.support_nodup
  let a := P.support.next x h1a
  let b := P.support.prev x h1a
  have h5: a ∈ P.support := by exact List.next_mem P.support x h1a
  have h6: b ∈ P.support := by exact List.prev_mem P.support x h1a
  have h5a: s(a,x) ∈ P.edges :=
  have h7: a ≠ b := by sorry

  sorry


lemma help (P: G.Walk u v) (h1: u ≠ v):
P.length > 1 ∨ P.length = 1 := sorry

lemma p_is_uv (P: G.Walk u v)(hl : P.length = 1)(he: G.Adj u v) :
P.support = {u,v} := sorry

lemma EndsNotConnectedToMatching {M :G.Subgraph}{p: G.Walk u v}
(h1: p.IsAugmentingPath M) (h2: x=u ∨ x = v):
¬M.Adj x y:= by sorry

theorem unique_edge_in_m' (hm : M.IsMatching) (M': SimpleGraph V) (P: G.Walk u v) (hp: P.IsAugmentingPath M) (hM': M'=(symmDiff M.spanningCoe P.toSubgraph.spanningCoe)) :
∀ (w : V), w ∈ P.support → ∃(x : V), x ∈ P.support → s(w,x) ∈ M'.edgeSet := by
  intro h1 h2
  --unfold ExistsUnique
  have h3a: u≠v ∧ u ∉ M.support ∧ v ∉ M.support := hp.ends_unsaturated
  have h3b: ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ P.edges → s(x,y) ∈ P.edges → (M.Adj w x ↔ ¬M.Adj x y) := hp.alternates
  have h4 : u ≠ v := by aesop
  let y := P.getVert 1
  have h32: ¬M.Adj u y := by
    have h33: u=u := by aesop
    have h33: u=u ∨ u = v := by aesop
    exact EndsNotConnectedToMatching hp h33
  --have h67: P.vertexSet.ncard > 1 := by aesop
  have h5: P.length > 1 ∨ P.length = 1 := help P h4
  cases h5 with

  | inl h5l =>
    cases P with
    | nil => contradiction
    | cons h q =>
    rename V => z
    have h8 : s(u,z) ∈ G.edgeSet := by aesop
    have h9: ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ q.edges → s(x,y) ∈ q.edges → (M.Adj w x ↔ ¬M.Adj x y) := sorry
    -- unfold h3 at hp
    -- let a := P.support.next h1 h2
    -- have h6: G.Adj h1 a :=  sorry --P.adj_getVert_succ
    -- have h7: s(h1,a) ∈ P.edgeSet := by sorry
    sorry
  | inr h5r =>

    have h12: P.vertexSet.ncard = 2 := by sorry
    have h13: G.Adj u v := P.adj_of_length_eq_one h5r
    let t:= h13.toWalk
    have h14: P.length <= 1:= by aesop
    have h15: P.getVert 1 = v := P.getVert_of_length_le h14
    have h16: v = y := by aesop
    have h17: ¬M.Adj u v := by exact Eq.mpr_not (congrArg (M.Adj u) h16) h32
    have h18: M'.Adj u v := by sorry
    have h19: P.support = {u,v} := by exact p_is_uv P h5r h13
    have h21: (h1 = u ∨ h1 = v) := by sorry
    cases h21 with
    | inl h =>
      simp
      use v
      have h22: v ∈ P.support := by exact end_mem_support P
      exact
      sorry
    | inr h =>
      simp
      use u
      have h19: u ∈ P.support := by exact start_mem_support P
      sorry

    --have h19: u ∈ P.support := by exact start_mem_support P
    --have h19: v ∈ P.support := by exact end_mem_support P
    --have h20: t ⊆ P := by aesop
    --have h18: {s(u,v)} = P.edges := by apply?

    -- cases P with
    -- | nil => contradiction
    -- | cons h q =>
    --   have h77: (cons h q).length = q.length + 1 := length_cons h q
    --   have h78: (cons h q).length = 1 := h5r
    --   have h79: q.length = 0 := by aesop
    --   have h80: q.Nil := by aesop
    --   have h81: q = Walk.nil.Nil := h80 @Nil.eq_nil -- nil_iff_eq_nil.mp

    -- -- have h17: singleton P h13 := sorry
    --   have h34: (cons h q) = Walk.cons h Nil :=
    --   have h16: (cons h q) = h.toWalk := by exact -- P.singleton_coe h13 --mk'_mem_edges_singleton


theorem unique_edge_in_m'_new (hm : M.IsMatching) (M': SimpleGraph V) (P: G.Walk u v) (hp: P.IsAugmentingPath M) (hM': M'=(symmDiff M.spanningCoe P.toSubgraph.spanningCoe)) :
∀ (w : V), w ∈ P.support → ∃!(x : V), x ∈ P.support → s(w,x) ∈ M'.edgeSet := by
  intro h1 h2
  unfold ExistsUnique
  have h3: u≠v ∧ u ∉ M.support ∧ v ∉ M.support := hp.ends_unsaturated
  have h4 : u ≠ v := by aesop
  cases P with
  | nil => contradiction
  | cons h q =>
  sorry

  -- exact
  -- have h3: ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ P.edges → s(x,y) ∈ P.edges → (M.Adj w x ↔ ¬M.Adj x y) := hp.alternates
  -- have h4: P.vertexSet.ncard > 1 := by exact
  -- let z:V := z ∈ P.support
  -- have h5: y ∈ P.support ∧ s(h1,y) ∈ P.edges :=


  --unfold P.IsAugmentingPath at hp
  --have h3: P.IsAlternatingPath := by aesop
  --have h4: Exists.intro (b:V) h5
  -- #check @Exists.intro
end Path
end Walk

theorem exists_distinct (P: G.Walk u v) (hp: P.IsAugmentingPath M) :
∃(w x: V), w ∈ P.support ∧ x ∈ P.support ∧ w ≠ x := by
  sorry

end SimpleGraph





  -- have h1: ∀ (v : p.toSubgraph.support), G.degree = 2 := p.IsCycle


  -- let F := (symmDiff M.spanningCoe M'.spanningCoe)
  -- -- intro p
  -- induction p with
  -- | nil =>
  -- intros
  -- sorry
  -- -- have h1: p.edgeSet.ncard := (p.edgeSet ∩ M.edgeSet).ncard
  -- -- have h2: p.edgeSet.ncard := (p.edgeSet ∩ M'.edgeSet).ncard
  -- -- have hp: (p.edgeSet ∩ M.edgeSet).ncard := 0
  -- -- rfl
  -- | cons h q ih => sorry




theorem component_edges_greater_than (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching) (he: M'.edgeSet.ncard > M.edgeSet.ncard):
∃ (cc: (symmDiff M.spanningCoe M'.spanningCoe).ConnectedComponent), (cc.componentAltPath M) ∧ ((cc.edgeSet ∩ M'.edgeSet).ncard > (cc.edgeSet ∩ M.edgeSet).ncard):=
  sorry

theorem exists_aug_path (M' : G.Subgraph) (hm : M.IsMatching) (hm' : M'.IsMatching):
∃ (p: (symmDiff M.spanningCoe M'.spanningCoe).Walk u v), (p.IsAugmentingPath M):=
sorry

theorem berge_left (M : G.Subgraph): (M.IsMaximumMatching) → ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M :=
  sorry
