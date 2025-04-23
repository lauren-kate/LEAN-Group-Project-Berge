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

namespace SimpleGraph.Walk

lemma PathVertexHasTwoNeighbours {p:G.Walk u v}(h:p.IsPath):
∀ x ,(x≠ u ∧ x ≠ v) → x ∈ p.support → ∃x₁ x₂, s(x₁ ,x) ∈ p.edges ∧ s(x,x₂) ∈ p.edges ∧ x₁ ≠ x₂:= by
  intro x h₁ h₂
  induction p with
  |nil=> aesop
  |@cons u v w hp q ih =>
    by_cases h3: (x=v)
    · cases q with
      |nil=> aesop
      |cons hq r =>
        rename V=>v'
        use u
        use v'
        aesop
    · aesop

lemma PathVertexHasOnlyTwoNeighbours {p:G.Walk u v}(h:p.IsPath):
∀ x ,(x≠ u ∧ x ≠ v) → x ∈ p.support → ∃x₁ x₂, (s(x₁ ,x) ∈ p.edges ∧ s(x,x₂) ∈ p.edges ∧ x₁ ≠ x₂ ∧ ∀y,s(x,y) ∈ p.edges→ (y = x₁ ∨ y = x₂)):= by
intro x h₁ h₂
induction p with
|nil => aesop
|@cons u v w hp q ih =>
  by_cases h3: (x =v)
  · cases q with
    |nil=>aesop
    |cons hq r=>
      rename V=> v'
      use u
      use v'
      apply And.intro
      · aesop
      · apply And.intro
        · aesop
        · apply And.intro
          · aesop
          · intro y h5
            subst h3
            by_contra h6
            have h7: s(x,y) ∈ (cons hq r).edges:= by aesop
            have h8: s(x,y) ∈ r.edges:= by aesop
            have h9: x ∈ r.support:= by exact fst_mem_support_of_mem_edges r h8
            have h10: (cons hq r).IsPath:= by exact IsPath.of_cons h
            by_cases h11: y= v'
            · aesop
            · aesop

  · aesop


lemma InPathNotEndpointinMatching {M: G.Subgraph}{p: G.Walk u v}
(h1: p.IsAugmentingPath M) (h2: ¬ (x=u ∨ x = v))(h3: x ∈ p.support): x ∈ M.support:= by
  refine (Subgraph.mem_support M).mpr ?_
  simp_all
  have h4: ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y):= by
    exact h1.alternates
  have h5: ∃x₁ x₂, s(x₁ ,x) ∈ p.edges ∧ s(x,x₂) ∈ p.edges ∧ x₁ ≠ x₂:= by
    refine PathVertexHasTwoNeighbours ?_ x h2 h3
    exact h1.toIsPath
  obtain ⟨x₁,x₂,h5⟩ := h5
  by_cases hM: M.Adj x₁ x
  · use x₁
    exact id (Subgraph.adj_symm M hM)
  · have h7: (M.Adj x₁ x ↔  ¬M.Adj x x₂):= by
      obtain ⟨h51,h52,h53⟩ := h5
      exact h4 h53 h51 h52
    aesop


lemma PathVertexAdjMatchingThenPath {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M)(h3:x ∈ p.support):
∀z, M.Adj x z → p.toSubgraph.Adj x z:= by
  intro z h4
  have h5: x ∈ M.verts:= by exact M.edge_vert h4
  have h6: ∃w, M.Adj x w ∧ ∀y, M.Adj x y → y = w:= by aesop
  have h7: M.Adj x z ∧ ∀ y, M.Adj x y → y = z:= by aesop
  have h8: ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y):= by exact h2.alternates
  have h8: ∀ w z : V, w ≠ z → s(w,x) ∈ p.edges → s(x,z) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x z):= by
    revert x
    exact fun {x} h3 z h4 h5 h6 h7 w a a_1 a_2 ↦ h8 a a_1 a_2
  have h5: x ∈ M.support:= by
    refine (SimpleGraph.Subgraph.mem_support M).mpr ?_
    use z
  show s(x,z) ∈ p.toSubgraph.edgeSet
  by_contra h9
  have h9: s(x,z) ∉ p.edges:=by aesop
  have hc: x≠u ∧ x ≠ v:=by
    have hc:(x=u ∨ x = v) → x ∉ M.support:= by
      exact fun a ↦ EndsAugPathMeansNotInM h2 x h3 a
    aesop
  revert h8
  simp
  have h8: ∃x₁ x₂, s(x₁ ,x) ∈ p.edges ∧ s(x,x₂) ∈ p.edges ∧ x₁ ≠ x₂:= by
    have h10: p.IsPath := by exact h2.toIsPath
    exact PathVertexHasTwoNeighbours h10 x hc h3
  obtain ⟨x₁,x₂,h8⟩:=h8
  use x₁,x₂
  apply And.intro
  · aesop
  · apply And.intro
    · aesop
    · apply And.intro
      · aesop
      · intro h
        obtain ⟨h71,h72⟩ := h7
        obtain ⟨h81,h82,h83⟩ := h8
        have h10: x₁ = z ∨ x₂ = z := by
          have h11: M.Adj x₁ x ∨ M.Adj x x₂ := by aesop
          cases h11 with
          |inl h11 =>
            have h12: M.Adj x x₁:= by exact id (Subgraph.adj_symm M h11)
            have h12: M.Adj x x₁ → x₁ = z:= by aesop
            have h13: x₁ = z:= by aesop
            left
            exact h13
          |inr h11 =>
            have h12: M.Adj x x₂ → x₂ = z:= by aesop
            have h13: x₂ = z:= by aesop
            right
            exact h13
        cases h10 with
        |inl h10 =>
          subst z
          have h11: s(x,x₁) = s(x₁,x):= by exact Sym2.eq_swap
          aesop
        |inr h10 =>
          subst z
          aesop


theorem AugPathMatchingNoNeighbours {M :G.Subgraph}{p: G.Walk u v}[Finite V]
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



lemma StartPointUniqueNeigbour {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h2: p.IsAugmentingPath M):
  ∃! w',(symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj u w':= by
  cases p with
  |nil =>
    have hc': u ≠ u:= by exact h2.ends_unsaturated.left
    aesop
  |cons h4 q =>
    rename V => w₂
    use w₂
    simp_all only [support_cons, List.mem_cons, true_or, Walk.toSubgraph]
    apply And.intro
    · unfold symmDiff
      right
      refine (sdiff_adj (G.subgraphOfAdj h4 ⊔ q.toSubgraph).spanningCoe M.spanningCoe u w₂).mpr ?_
      apply And.intro
      · simp
      · let p' := cons h4 q
        have h5: u ∉ M.support:= by exact h2.ends_unsaturated.right.left
        intro h6
        simp_all
        have h6: ∃z,M.Adj u z:= by aesop
        have h6: u ∈ M.support:= by exact h6
        contradiction
    · unfold symmDiff
      intro y h3
      by_contra hc
      revert h3
      simp
      apply And.intro
      · have h5: ¬ M.Adj u y:= by
          have h6: u ∉ M.support:= by exact h2.ends_unsaturated.right.left
          intro h7
          have h7:∃z,M.Adj u z:= by aesop
          contradiction
        intro h6
        contradiction
      · intro a
        cases a with
        | inl h =>
          cases h with
          | inl h_1 =>
            subst h_1
            simp_all only [not_true_eq_false]
          | inr h_2 => simp_all only [not_true_eq_false]
        | inr h_1 =>
          have h5: u ∈ q.support:= by
            have h6: u ∈ q.toSubgraph.support:= by
              refine (Subgraph.mem_support q.toSubgraph).mpr ?_
              use y
            have h6:u ∈ q.toSubgraph.verts:= by exact q.toSubgraph.edge_vert h_1
            exact (mem_verts_toSubgraph q).mp h6
          have h7: ¬(cons h4 q).IsPath:=by
            have h8: (cons h4 q).IsPath ↔ q.IsPath ∧ u ∉ q.support:= by exact cons_isPath_iff h4 q
            aesop
          have h7c: (cons h4 q).IsPath:=by exact h2.toIsPath
          contradiction


--- Lemma for Lauren's node above mine
theorem AugPathUniqueNeighbourInAugPath {M :G.Subgraph}{p: G.Walk u v}[Finite V]
(h1: M.IsMatching)(h2: p.IsAugmentingPath M) :
∀w : V, w∈p.support → ∃! w',(symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj w w' := by
  intro w hp
  by_cases h3 : (w=u ∨ w = v)
  · cases h3 with
    |inl h3 =>
      subst h3
      exact StartPointUniqueNeigbour h2
    |inr h3 =>
      let p':= p.reverse
      subst h3
      have h4:p.reverse.IsAugmentingPath M:=by exact ReverseAugmentingPathAugmenting h2
      have h5:∃! w', (symmDiff M.spanningCoe p'.toSubgraph.spanningCoe).Adj w w':=by
        exact StartPointUniqueNeigbour h4
      have h6:p'.toSubgraph.spanningCoe = p.toSubgraph.spanningCoe:=by aesop
      aesop
  · have h4:∃x₁ x₂, s(x₁ ,w) ∈ p.edges ∧ s(w,x₂) ∈ p.edges ∧ x₁ ≠ x₂:= by
      refine PathVertexHasTwoNeighbours ?_ w ?_ hp
      · exact h2.toIsPath
      · aesop
    obtain ⟨w',w'',h4⟩:= h4
    have h5: (M.Adj w' w ↔  ¬M.Adj w w''):= by
      have hM: ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y):= by
        exact h2.alternates
      obtain ⟨h41,h42,h43⟩ := h4
      exact hM h43 h41 h42
    by_cases h6: M.Adj w' w
    · use w''
      simp
      apply And.intro
      · unfold symmDiff
        right
        simp
        apply And.intro
        · refine Subgraph.mem_edgeSet.mp ?_
          aesop
        · aesop
      · intro y h7
        by_cases h8: y ∈ p.support
        · cases h7 with
          |inl h7=>
            simp at h7
            obtain ⟨h71,h72⟩:= h7
            have h9: p.toSubgraph.Adj w y:= by exact PathVertexAdjMatchingThenPath h1 h2 hp y h71
            contradiction
          |inr h7=>
            simp at h7
            have h9: s(w,y) ∈ p.edges:= by
              refine (mem_edges_toSubgraph p).mp ?_
              obtain ⟨h7,_⟩ :=h7
              exact h7
            have h10: y=w'' ∨ y = w':=by
              by_contra h10
              simp_all
              have h11: ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y):= by exact h2.alternates
              have h11: w'' ≠ y → s(w'',w) ∈ p.edges → s(w,y) ∈ p.edges → (M.Adj w'' w ↔ ¬M.Adj w y):= by exact fun a a_1 a_2 ↦ h11 a a_1 h9
              simp at h11
              have hswap1: ¬y = w'':= by aesop
              have hswap2: s(w'',w) ∈ p.edges := by
                refine (mem_edges_toSubgraph p).mp ?_
                refine Subgraph.mem_edgeSet.mpr ?_
                have h11: p.toSubgraph.Adj w w'':= by
                  refine Subgraph.mem_edgeSet.mp ?_
                  refine (mem_edges_toSubgraph p).mpr ?_
                  exact h4.right.left
                exact id (Subgraph.adj_symm p.toSubgraph h11)
              have hswap3: ¬M.Adj w'' w:= by exact fun a ↦ h5 (id (Subgraph.adj_symm M a))
              aesop
            cases h10 with
            |inl h10=> exact h10
            |inr h10=>
              subst h10
              obtain ⟨_,h7⟩:= h7
              exact False.elim (h7 (id (Subgraph.adj_symm M h6)))
        · have h9: ¬ (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj w y:=by exact AugPathMatchingNoNeighbours h1 h2 w y hp h8
          contradiction
    · use w'
      simp
      apply And.intro
      · unfold symmDiff
        right
        simp
        apply And.intro
        · refine Subgraph.adj_symm p.toSubgraph ((fun {V} {G} {G'} {v w} ↦ Subgraph.mem_edgeSet.mp) ?_)
          exact h4.left
        · exact fun a ↦ h6 (id (Subgraph.adj_symm M a))
      · intro y h7
        by_cases h8: y ∈ p.support
        · cases h7 with
          |inl h7=>
            simp at h7
            obtain ⟨h71,h72⟩:=h7
            have h71: p.toSubgraph.Adj w y:= by exact PathVertexAdjMatchingThenPath h1 h2 hp y h71
            contradiction
          |inr h7=>
            simp at h7
            have h9: s(w,y) ∈ p.edges:= by
              refine (mem_edges_toSubgraph p).mp ?_
              obtain ⟨h7,_⟩ :=h7
              exact h7
            have h10:y=w'' ∨ y = w':= by
              by_contra h10
              simp_all
              have h11: ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y):= by exact h2.alternates
              have h11: w' ≠ y → s(w',w) ∈ p.edges → s(w,y) ∈ p.edges → (M.Adj w' w ↔ ¬M.Adj w y):= by exact fun a a_1 a_2 ↦ h11 a a_1 h9
              aesop
            cases h10 with
            |inl h10=>
              aesop
            |inr h10=> exact h10
        · have h9: ¬ (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).Adj w y:= by exact AugPathMatchingNoNeighbours h1 h2 w y hp h8
          contradiction
