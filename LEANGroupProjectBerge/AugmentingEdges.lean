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




lemma cons_edgeset_card [Finite V] {u v w : V} {F : SimpleGraph V} (h : F.Adj u v) (p : F.Walk v w) :
    s(u,v) ∉ p.edges → (Walk.cons h p).toSubgraph.edgeSet.ncard = p.toSubgraph.edgeSet.ncard + 1 := by
  have := Fintype.ofFinite V
  have : (Walk.cons h p).toSubgraph.edgeSet = insert s(u,v) p.toSubgraph.edgeSet := by aesop
  rw [this]
  intro h
  have : s(u,v) ∉ p.toSubgraph.edgeSet := by aesop
  exact Set.ncard_insert_of_not_mem this



lemma cons_matched_edgeset_card [Finite V] {u v w : V} {F : SimpleGraph V} (h_m : M.Adj u v) (h_f : F.Adj u v) (p : F.Walk v w) :
    s(u,v) ∉ p.edges →
    (M.edgeSet ∩ (Walk.cons h_f p).toSubgraph.edgeSet).ncard = (M.edgeSet ∩ p.toSubgraph.edgeSet).ncard + 1 := by
  have := Fintype.ofFinite V
  have : M.edgeSet ∩ (Walk.cons h_f p).toSubgraph.edgeSet = insert s(u,v) (M.edgeSet ∩ p.toSubgraph.edgeSet) := by aesop
  rw [this]
  intro h
  have : s(u,v) ∉ M.edgeSet ∩ p.toSubgraph.edgeSet := by aesop
  exact Set.ncard_insert_of_not_mem this



lemma path_cons_nodup {u v w : V} {F : SimpleGraph V} (h_f : F.Adj u v) (p : F.Walk v w) :
    (Walk.cons h_f p).IsPath → s(u, v) ∉ p.edges := by
  intro h_path
  have : (∀ (e : Sym2 V), e ∈ p.edges → s(u,v) ≠ e ) := (List.pairwise_cons.mp h_path.edges_nodup).1
  intro h_edge
  have := this s(u,v) h_edge
  contradiction


lemma path_single_edgeset {u v w : V} {F : SimpleGraph V} {p : F.Walk w v} (h_eq : w=v) (h_adj : F.Adj u w):
    (Walk.cons h_adj p).IsPath → (Walk.cons h_adj p).toSubgraph.edgeSet = {s(u,w)} := by
  aesop




lemma aug_card [Finite V] {u v : V} {F : SimpleGraph V} (p : F.Walk u v) :
    u≠v → v ∉ M.support → p.IsAlternatingPath M →
    (M.Adj u (p.getVert 1) → p.toSubgraph.edgeSet.ncard = 2*(M.edgeSet ∩ p.toSubgraph.edgeSet).ncard )
    ∧ (¬M.Adj u (p.getVert 1) → p.toSubgraph.edgeSet.ncard = 2*(M.edgeSet ∩ p.toSubgraph.edgeSet).ncard + 1) := by
  induction p with
  | nil =>
    intros
    contradiction
  | cons h_adj q ih =>
    rename_i u w v
    intros h_unv h_vunsat h_consalt
    have h_q_alt : q.IsAlternatingPath M := alt_of_cons h_consalt
    let p := Walk.cons h_adj q
    let EP := p.toSubgraph.edgeSet
    let EMandP := M.edgeSet ∩ p.toSubgraph.edgeSet
    apply And.intro
    · show M.Adj u (p.getVert 1) → EP.ncard = 2*EMandP.ncard
      intro h_endmatch
      match em (w=v) with
      | Or.inl h_eq =>
        have : p.getVert 1 = v := by aesop
        rw [this] at h_endmatch
        have : v∈ M.support := M.mem_support.mpr ⟨u, M.adj_symm h_endmatch⟩
        contradiction
      | Or.inr h_neq =>
        let EQ := q.toSubgraph.edgeSet
        let EMandQ := M.edgeSet ∩ q.toSubgraph.edgeSet
        specialize ih h_neq h_vunsat h_q_alt
        change  (M.Adj w (q.getVert 1) → EQ.ncard = 2 * EMandQ.ncard) ∧
                (¬M.Adj w (q.getVert 1) → EQ.ncard = 2 * EMandQ.ncard + 1) at ih
        have h_u_nodup : u ≠ q.getVert 1 := by
          cases q with
          | nil => contradiction
          | cons h_adj' q' =>
            let x := (Walk.cons h_adj' q').getVert 1
            exact (List.pairwise_cons.mp h_consalt.support_nodup).1 x (by aesop)
        have h_w_edge : s(w, q.getVert 1) ∈ p.edges := by
          cases q with
          | nil => contradiction
          | cons h_adj' q' => aesop
        have heq : p.getVert 1 = w := by aesop
        rw [heq] at h_endmatch
        replace ih := ih.2  ((h_consalt.alternates h_u_nodup (by aesop) h_w_edge).mp h_endmatch)
        have h_uw_not_q : s(u,w) ∉ q.edges := path_cons_nodup h_adj q h_consalt.toIsPath
        have h_p_add : EP.ncard = EQ.ncard + 1 := cons_edgeset_card h_adj q h_uw_not_q
        have h_pm_add : EMandP.ncard = EMandQ.ncard + 1 := cons_matched_edgeset_card h_endmatch h_adj q h_uw_not_q
        rw [h_p_add, h_pm_add]
        omega
    · show ¬M.Adj u (p.getVert 1) → EP.ncard = 2*EMandP.ncard + 1
      intro h_uunsat
      match em (w=v) with
      | Or.inl h_eq =>
        have h_ep_single : EP = {s(u,w)} := path_single_edgeset h_eq h_adj h_consalt.toIsPath
        have h_uw_unmatch : s(u,w) ∉ M.edgeSet := by aesop
        have : EMandP = {} := by
          unfold EMandP; unfold EP at h_ep_single
          rw [h_ep_single]
          aesop
        aesop
      | Or.inr h_neq =>
        let EQ := q.toSubgraph.edgeSet
        let EMandQ := M.edgeSet ∩ q.toSubgraph.edgeSet
        specialize ih h_neq h_vunsat h_q_alt
        change  (M.Adj w (q.getVert 1) → EQ.ncard = 2 * EMandQ.ncard) ∧
                (¬M.Adj w (q.getVert 1) → EQ.ncard = 2 * EMandQ.ncard + 1) at ih
        have h_u_nodup : u ≠ q.getVert 1 := by
          cases q with
          | nil => contradiction
          | cons h_adj' q' =>
            let x := (Walk.cons h_adj' q').getVert 1
            exact (List.pairwise_cons.mp h_consalt.support_nodup).1 x (by aesop)
        have h_w_edge : s(w, q.getVert 1) ∈ p.edges := by
          cases q with
          | nil => contradiction
          | cons h_adj' q' => aesop
        have heq : p.getVert 1 = w := by aesop
        rw [heq] at h_uunsat
        have h' : M.Adj w (q.getVert 1) := by
          let x := q.getVert 1
          have h_wx_edge : s(w, x) ∈ p.edges := by aesop
          have h_ux_edge : s(u, w) ∈ p.edges := by aesop
          have := h_consalt.alternates h_u_nodup h_ux_edge h_wx_edge
          aesop
        replace ih := ih.left h'
        have h_mpq : EMandP = EMandQ := by aesop
        rw [←h_mpq] at ih
        rw [←ih]
        have : s(u,w) ∉ q.edges := path_cons_nodup h_adj q h_consalt.toIsPath
        exact cons_edgeset_card h_adj q this





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



lemma aug_path_card [Finite V] {u v : V} {p : G.Walk u v} (h : p.IsAugmentingPath M):
    p.toSubgraph.edgeSet.ncard = 2*(M.edgeSet ∩ p.toSubgraph.edgeSet).ncard + 1 := by
  have : ¬M.Adj u (p.getVert 1) → p.toSubgraph.edgeSet.ncard = 2*(M.edgeSet ∩ p.toSubgraph.edgeSet).ncard + 1 :=
    (aug_card p h.ends_unsaturated.1 h.ends_unsaturated.2.2 h.toIsAlternatingPath).2
  apply this
  have : u ∉ M.support := h.ends_unsaturated.2.1
  intro h_adj
  exact this (M.mem_support.mpr ⟨p.getVert 1, h_adj⟩)



lemma symm_diff_edgeset (G' : SimpleGraph V) : (symmDiff G G').edgeSet = symmDiff G.edgeSet G'.edgeSet :=
  Set.ext (Sym2.ind (fun _ _ => Iff.rfl))



theorem aug_symm_diff_gt [Finite V] {u v : V} {p : G.Walk u v} (h : p.IsAugmentingPath M):
  (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard > M.edgeSet.ncard := by
  have hs : (H : G.Subgraph) → H.spanningCoe.edgeSet = H.edgeSet := fun _ => rfl
  rw [symm_diff_edgeset]
  repeat rw [hs]
  rw [symm_diff_card, aug_path_card h]
  omega
