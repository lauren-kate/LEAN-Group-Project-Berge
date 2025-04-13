import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import Mathlib.Logic.Basic
import Mathlib.Data.Set.Card

import LEANGroupProjectBerge.Basic
import LEANGroupProjectBerge.SymDiffEvenCycle

namespace SimpleGraph

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M M': G.Subgraph}
variable {u v w: V}


namespace Walk

--Placeholder from Josh -> changed brackets around h as failed to synthesize w/o
theorem IfBerge{M:G.Subgraph}(h: M.IsMatching)[Finite V]:
(∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M) → ¬ M.IsMaximumMatching := sorry


--Placeholder!!!
-- exists an augmenting path in F -
theorem matching_symmdiff_gt_aug [Finite V] (h_M_match : M.IsMatching) (h_M'_match : M'.IsMatching) (h_e_gt : M'.edgeSet.ncard > M.edgeSet.ncard):
    ∃ (u v : V) (p : (symmDiff M.spanningCoe M'.spanningCoe).Walk u v), p.IsAugmentingPath M := by
  sorry


lemma matching_not_max_aug_h5_hl_hr [Finite V] (M:G.Subgraph) (x y:V) (h:M.spanningCoe.Adj x y): G.Adj x y :=
  have h1: M.Adj x y := by aesop
  have h2: G.Adj x y := M.adj_sub h1
  h2

theorem matching_not_max_aug [Finite V] (h_M_match : M.IsMatching) (h_M_nmax : ¬M.IsMaximumMatching) :
    ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M :=

     have h1: ¬(M.IsMatching ∧  ¬(∃ N : G.Subgraph, N.IsMatching ∧ M.edgeSet.encard < N.edgeSet.encard)):= sorry --Literally the definition of maximum matching but for some reason I can't figure this out
     have h2: ¬M.IsMatching ∨  ¬(¬∃ N : G.Subgraph, N.IsMatching ∧ M.edgeSet.encard < N.edgeSet.encard):= by aesop
     have h3: ¬(¬∃ N : G.Subgraph, N.IsMatching ∧ M.edgeSet.encard < N.edgeSet.encard) := by aesop
     have h4: ∃ N : G.Subgraph, N.IsMatching ∧ M.edgeSet.encard < N.edgeSet.encard := by aesop
     have h4: ∃ N : G.Subgraph, N.IsMatching ∧ M.edgeSet.ncard < N.edgeSet.ncard := by
        obtain ⟨ N, H4 ⟩ := h4
        exact(
          -- have hM: M.edgeSet.Finite := sorry --????
          -- have hN: N.edgeSet.Finite := sorry --????
          have h5: M.edgeSet.encard < N.edgeSet.encard := And.right H4
          have h6: M.edgeSet.encard.toNat ≤   N.edgeSet.encard.toNat := sorry

          sorry --Since M and N are finite? - don't know how to show
        )
     have h5: ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M := by
          obtain ⟨ M', H4 ⟩ := h4
          let F:=symmDiff M.spanningCoe M'.spanningCoe
          have h5: ∃ (u v : V) (p : F.Walk u v), p.IsAugmentingPath M := matching_symmdiff_gt_aug h_M_match (And.left H4) (And.right H4)

          have h6: F ≤ G := by
               intro x y
               exact
                    fun h7: F.Adj x y =>
                    have h8: s(x,y) ∈ F.edgeSet := by aesop
                    have h9: s(x,y) ∈ M.spanningCoe.edgeSet ∧ s(x,y) ∉ M'.spanningCoe.edgeSet ∨ s(x,y) ∈ M'.spanningCoe.edgeSet ∧ s(x,y) ∉ M.spanningCoe.edgeSet := by aesop
                    have h10: s(x,y) ∈ M.spanningCoe.edgeSet ∨ s(x,y) ∈ M'.spanningCoe.edgeSet := by aesop
                    have h11: M.spanningCoe.Adj x y ∨ M'.spanningCoe.Adj x y := by aesop
                    have h10: G.Adj x y := by
                         cases h11 with
                         | inl hl => exact matching_not_max_aug_h5_hl_hr M x y hl
                         | inr hr => exact matching_not_max_aug_h5_hl_hr M' x y hr
                    h10

          have h7: ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M := by
               obtain ⟨ u, v, p, H5 ⟩ := h5
               exact(
                    have q: G.Walk u v :=  p.map (.ofLE h6)
                    have h8: q.IsAugmentingPath M := sorry-- Comes from H5 i think
                    have h9: ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M := by aesop
                    h9
               )

          exact h7
     h5



theorem BergesTheorem [Finite V] (M : G.Subgraph){h: M.IsMatching}:  M.IsMaximumMatching ↔ ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M :=
  have h1: ¬M.IsMaximumMatching ↔ (∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M) := {
    mp := matching_not_max_aug h
    mpr := IfBerge h
  }
  have h2: M.IsMaximumMatching ↔ ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M := by aesop
  h2
