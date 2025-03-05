import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import LEANGroupProjectBerge.Basic

namespace SimpleGraph


universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M : G.Subgraph}




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



lemma aug_card [Finite V] {u v : V} {F : SimpleGraph V} (p : F.Walk u v) (hm : M.IsMatching) :
    u≠v → v ∉ M.support → p.IsAlternatingPath M →
    (M.Adj u (p.getVert 1) → p.toSubgraph.edgeSet.ncard = 2*(M.edgeSet ∩ p.toSubgraph.edgeSet).ncard )
    ∧ (¬M.Adj u (p.getVert 1) → p.toSubgraph.edgeSet.ncard = 2*(M.edgeSet ∩ p.toSubgraph.edgeSet).ncard + 1) := by
  induction p with
  | nil =>
    intros
    contradiction
  | cons h_adj p' ih =>
    rename_i u w v
    intros h_unv h_vunsat h_consalt
    have h_p'alt : p'.IsAlternatingPath M := alt_of_cons h_consalt
    let p := Walk.cons h_adj p'
    let EP := p.toSubgraph.edgeSet
    let EPnM := M.edgeSet ∩ p.toSubgraph.edgeSet
    apply And.intro
    · show M.Adj u (p.getVert 1) → EP.ncard = 2*EPnM.ncard
      intro h_endmatch
      match em (w=v) with
      | Or.inl h_eq =>
        have : p.getVert 1 = v := by aesop
        rw [this] at h_endmatch
        have : v∈ M.support := M.mem_support.mpr ⟨u, M.adj_symm h_endmatch⟩
        contradiction
      | Or.inr h_neq =>
        let EP' := p'.toSubgraph.edgeSet
        let EP'andM := M.edgeSet ∩ p'.toSubgraph.edgeSet
        specialize ih h_neq h_vunsat h_p'alt
        change  (M.Adj w (p'.getVert 1) → EP'.ncard = 2 * EP'andM.ncard) ∧
                (¬M.Adj w (p'.getVert 1) → EP'.ncard = 2 * EP'andM.ncard + 1) at ih
        have h1 : u ≠ p'.getVert 1 := by sorry
        have h3 : s(w, p'.getVert 1) ∈ p.edges := by sorry
        have heq : p.getVert 1 = w := by aesop
        rw [heq] at h_endmatch
        replace ih := ih.2  ((h_consalt.alternates h1 (by aesop) h3).mp h_endmatch)
        sorry
    · show ¬M.Adj u (p.getVert 1) → EP.ncard = 2*EPnM.ncard + 1
      intro h_uunsat
      sorry





lemma symm_diff_card (α : Type u) (A B : Set α) [Finite A] [Finite B] : (symmDiff A B).ncard = A.ncard + B.ncard - 2*(A ∩ B).ncard := by
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



lemma aug_path_card [Finite V] {u v : V} {p : G.Walk u v} (h : p.IsAugmentingPath M) (hm : M.IsMatching):
    p.toSubgraph.edgeSet.ncard = 2*(M.edgeSet ∩ p.toSubgraph.edgeSet).ncard + 1 := by
  have : ¬M.Adj u (p.getVert 1) → p.toSubgraph.edgeSet.ncard = 2*(M.edgeSet ∩ p.toSubgraph.edgeSet).ncard + 1 :=
    (aug_card p hm h.ends_unsaturated.1 h.ends_unsaturated.2.2 h.toIsAlternatingPath).2
  apply this
  have : u ∉ M.support := h.ends_unsaturated.2.1
  intro h_adj
  exact this (M.mem_support.mpr ⟨p.getVert 1, h_adj⟩)



lemma symm_diff_edgeset (G' : SimpleGraph V) : (symmDiff G G').edgeSet = symmDiff G.edgeSet G'.edgeSet :=
  Set.ext (Sym2.ind (fun _ _ => Set.mem_def))



theorem aug_symm_diff_gt [Finite V] {u v : V} {p : G.Walk u v} (h : p.IsAugmentingPath M) (hm : M.IsMatching):
  (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard > M.edgeSet.ncard := by
  have hs : (H : G.Subgraph) → H.spanningCoe.edgeSet = H.edgeSet := fun _ => rfl
  rw [symm_diff_edgeset]
  repeat rw [hs]
  rw [symm_diff_card]
  rw [aug_path_card h hm]
  omega
