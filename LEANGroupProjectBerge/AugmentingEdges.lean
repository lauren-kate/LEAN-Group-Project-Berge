import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import LEANGroupProjectBerge.Basic
import LEANGroupProjectBerge.AlternatingProperties

namespace SimpleGraph


universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M : G.Subgraph}


lemma symm_diff_card {α : Type u} (A B : Set α) [Finite A] [Finite B] : (symmDiff A B).ncard = A.ncard + B.ncard - 2*(A ∩ B).ncard := by
  rw [symmDiff_eq_sup_sdiff_inf]; simp
  have : ((A ∪ B) \ (A ∩ B)).ncard + (A ∩ B).ncard = ((A ∪ B) ∪ (A ∩ B)).ncard := Set.ncard_diff_add_ncard (A ∪ B) (A ∩ B)
  replace this : ((A ∪ B) \ (A ∩ B)).ncard = ((A ∪ B) ∪ (A ∩ B)).ncard - (A ∩ B).ncard := by omega
  rw [this]
  replace this : (A ∪ B) ∪ (A ∩ B) = (A ∪ B) := Set.ext (by aesop)
  rw [this]
  replace this : (A ∪ B).ncard + (A ∩ B).ncard = A.ncard + B.ncard := Set.ncard_union_add_ncard_inter A B
  replace this : (A ∪ B).ncard = A.ncard + B.ncard - (A ∩ B).ncard := by omega
  rw [this]
  omega



lemma symm_diff_edgeset (G' : SimpleGraph V) : (symmDiff G G').edgeSet = symmDiff G.edgeSet G'.edgeSet :=
  Set.ext (Sym2.ind (fun _ _ => Iff.rfl))



theorem aug_symm_diff_gt [Finite V] {u v : V} {p : G.Walk u v} (h : p.IsAugmentingPath M):
  (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard > M.edgeSet.ncard := by
  have hs : (H : G.Subgraph) → H.spanningCoe.edgeSet = H.edgeSet := fun _ => rfl
  rw [symm_diff_edgeset]
  repeat rw [hs]
  rw [symm_diff_card, ←p.edgeSet_toSubgraph_eq, aug_path_edgeset_inter h]
  omega
