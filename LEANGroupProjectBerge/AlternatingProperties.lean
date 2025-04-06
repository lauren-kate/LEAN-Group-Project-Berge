import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import LEANGroupProjectBerge.Basic


namespace SimpleGraph


universe u
variable {V : Type u}
variable {F G : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w : V}


namespace Walk

def alternates (p : F.Walk u v) (M : G.Subgraph) : Prop :=
  ∀ ⦃w x y: V⦄, w ≠ y → s(w,x) ∈ p.edges → s(x,y) ∈ p.edges → (M.Adj w x ↔ ¬M.Adj x y)



lemma alt_of_cons' {h : F.Adj u v} {p : F.Walk v w} :
    (Walk.cons h p).alternates M → p.alternates M := by
  intro h_alt w x y h_wy h_wx h_xy
  have : {e : Sym2 V} → e ∈ p.edges → e ∈ (cons h p).edges := by aesop
  exact h_alt h_wy (this h_wx) (this h_xy)


lemma alt_of_reverse (p : F.Walk u v) : p.alternates M → p.reverse.alternates M := by
  sorry


lemma single_edgeset (p : F.Walk u v) : p.edges = [s(u,v)] → p.edgeSet = {s(u,v)} := by
  sorry


lemma cons_last_edge (p : F.Walk v w) (h_adj : F.Adj u v) (h_nnil : p.edges ≠ []) :
    p.edges.getLast h_nnil = (cons h_adj p).edges.getLast (by aesop) := by
  simp_all only [edges_cons, ne_eq, not_false_eq_true, List.getLast_cons]


lemma trail_cons_alt_edge {p : F.Walk v w}  (h_adj : F.Adj u v) (h_nnil : p.edges ≠ []) :
    (cons h_adj p).alternates M →
    (cons h_adj p).IsTrail →
    ( p.edges.head h_nnil ∈ M.edgeSet ↔ (cons h_adj p).edges.head (by aesop) ∉ M.edgeSet ) := by
  intro h_alt h_tr
  have : ∃ w x y : V, w≠y ∧ s(w,x) = (cons h_adj p).edges.head (by aesop) ∧ s(x,y) = p.edges.head h_nnil := by
    cases p with
    | nil => contradiction
    | cons h_adj' q =>
      rename V => v'
      exists u, v, v'
      have : u ≠ v' := by intro h; aesop
      exact ⟨this, rfl, rfl⟩
  obtain ⟨w,x,y, h_wy, h_wx_eq, h_xy_eq⟩ := this
  rw[←h_wx_eq, ←h_xy_eq]
  have h_wx_e : s(w,x) ∈ (cons h_adj p).edges := by aesop
  have h_wy_e : s(x,y) ∈ (cons h_adj p).edges := by aesop
  exact iff_not_comm.mp <| h_alt h_wy h_wx_e h_wy_e


lemma trail_cons_edgeset_ncard {p : F.Walk v w} {h_adj : F.Adj u v} (h_tr : (cons h_adj p).IsTrail) :
    (cons h_adj p).edgeSet.ncard = p.edgeSet.ncard + 1 := by
  sorry


lemma trail_cons_edgeset_inter_ncard_plus {s : Set (Sym2 V)} {p : F.Walk v w} {h_adj : F.Adj u v} (h_tr : (cons h_adj p).IsTrail) (h_mem : s(u,v) ∈ s) :
    (s ∩ (cons h_adj p).edgeSet).ncard = (s ∩ p.edgeSet).ncard + 1 := by
  sorry


lemma trail_cons_edgeset_inter_ncard_eq {s : Set (Sym2 V)} {p : F.Walk v w} {h_adj : F.Adj u v} (h_tr : (cons h_adj p).IsTrail) (h_mem : s(u,v) ∉ s) :
    (s ∩ (cons h_adj p).edgeSet).ncard = (s ∩ p.edgeSet).ncard := by
  sorry



mutual
  theorem alt_ends_match_unmatch [Finite V] {F : SimpleGraph V} {u v : V} (p : F.Walk u v) (h_tr : p.IsTrail) (h_alt : p.alternates M) :
      (h_nnil : p.edges ≠ []) →
      p.edges.getLast h_nnil ∉ M.edgeSet →
      p.edges.head h_nnil ∈ M.edgeSet →
      p.edgeSet.ncard = 2*(M.edgeSet ∩ p.edgeSet).ncard := by
    intro h_nnil h_lst_unmatch h_fst_match
    cases p with
    | nil => contradiction
    | cons h_adj q =>
      rename V => w
      let p := cons h_adj q
      if h_q_nil : q.edges = [] then
        aesop
      else
        have ih := alt_ends_unmatch_unmatch q (IsTrail.of_cons h_tr) (alt_of_cons' h_alt) h_q_nil
        have h_pq_end : q.edges.getLast h_q_nil = p.edges.getLast h_nnil := q.cons_last_edge h_adj h_q_nil
        have : q.edges.head h_q_nil ∉ M.edgeSet := (iff_not_comm.mp (trail_cons_alt_edge h_adj h_q_nil h_alt h_tr)).mp h_fst_match
        specialize ih (h_pq_end ▸ h_lst_unmatch) this
        show p.edgeSet.ncard = 2*(M.edgeSet ∩ p.edgeSet).ncard
        have : p.edgeSet.ncard = q.edgeSet.ncard + 1 := trail_cons_edgeset_ncard h_tr
        have : (M.edgeSet ∩ p.edgeSet).ncard = (M.edgeSet ∩ q.edgeSet).ncard + 1 := trail_cons_edgeset_inter_ncard_plus h_tr h_fst_match
        omega


  theorem alt_ends_unmatch_unmatch [Finite V] {F : SimpleGraph V} {u v : V} (p : F.Walk u v) (h_tr : p.IsTrail) (h_alt : p.alternates M) :
      (h_nnil : p.edges ≠ []) →
      p.edges.getLast h_nnil ∉ M.edgeSet →
      p.edges.head h_nnil ∉ M.edgeSet →
      p.edgeSet.ncard = 2*(M.edgeSet ∩ p.edgeSet).ncard + 1 := by
    intro h_nnil h_lst_unmatch h_fst_unmatch
    cases p with
    | nil => contradiction
    | cons h_adj q =>
      rename V => w
      let p := cons h_adj q
      if h_q_nil : q.edges = [] then
        cases q with
        | nil => -- base case
          have h_ep : p.edgeSet = {s(u,v)} := p.single_edgeset rfl
          have h_emp : M.edgeSet ∩ p.edgeSet = ∅ := by aesop
          rw[h_emp, h_ep]
          aesop
        | cons h_adj' r => contradiction
      else
        have ih := alt_ends_match_unmatch q (IsTrail.of_cons h_tr) (alt_of_cons' h_alt) h_q_nil
        have h_pq_end : q.edges.getLast h_q_nil = p.edges.getLast h_nnil := q.cons_last_edge h_adj h_q_nil
        have : q.edges.head h_q_nil ∈ M.edgeSet := (trail_cons_alt_edge h_adj h_q_nil h_alt h_tr).mpr h_fst_unmatch
        specialize ih (h_pq_end ▸ h_lst_unmatch) this
        show p.edgeSet.ncard = 2*(M.edgeSet ∩ p.edgeSet).ncard + 1
        have : p.edgeSet.ncard = q.edgeSet.ncard + 1 := trail_cons_edgeset_ncard h_tr
        have : (M.edgeSet ∩ p.edgeSet).ncard = (M.edgeSet ∩ q.edgeSet).ncard := trail_cons_edgeset_inter_ncard_eq h_tr h_fst_unmatch
        omega
end


theorem alt_ends_unmatch_match [Finite V] {F : SimpleGraph V} {u v : V} (p : F.Walk u v) (h_tr : p.IsTrail) (h_alt : p.alternates M) :
    (h_nnil : p.edges ≠ []) →
    p.edges.getLast h_nnil ∈ M.edgeSet →
    p.edges.head h_nnil ∉ M.edgeSet →
    p.edgeSet.ncard = 2*(M.edgeSet ∩ p.edgeSet).ncard := by
  intro h_nnil h_lst_match h_fst_unmatch
  let p' := p.reverse
  have h_nnil' : p'.edges ≠ [] := by aesop
  have h_p'_last_p_head : p'.edges.getLast h_nnil' = p.edges.head h_nnil := by
    simp_all only [edges_reverse, List.getLast_reverse, p']
  have h_p'_head_p_last : p'.edges.head h_nnil' = p.edges.getLast h_nnil := by
    simp_all only [edges_reverse, List.head_reverse, p']
  rw [←h_p'_head_p_last] at h_lst_match
  rw [←h_p'_last_p_head] at h_fst_unmatch
  have h_p' := alt_ends_match_unmatch p' ((reverse_isTrail_iff p).mpr h_tr) (p.alt_of_reverse h_alt) h_nnil' h_fst_unmatch h_lst_match
  have : p.edgeSet = p'.edgeSet := by
    unfold Walk.edgeSet
    rw[edges_reverse]
    aesop
  aesop


theorem alt_ends_match_match [Finite V] {F : SimpleGraph V} {u v : V} (p : F.Walk u v) (h_tr : p.IsTrail) (h_alt : p.alternates M) :
    (h_nnil : p.edges ≠ []) →
    p.edges.getLast h_nnil ∈ M.edgeSet →
    p.edges.head h_nnil ∈ M.edgeSet →
    p.edgeSet.ncard + 1 = 2*(M.edgeSet ∩ p.edgeSet).ncard := by
  intro h_nnil h_lst_match h_fst_match
  cases p with
  | nil => contradiction
  | cons h_adj q =>
    rename V => w
    let p := cons h_adj q
    if h_q_nil : q.edges = [] then
      cases q with
      | nil => --base case
        have h_ep : p.edgeSet = {s(u,v)} := p.single_edgeset rfl
        have h_emp : M.edgeSet ∩ p.edgeSet = {s(u,v)} := by aesop
        rw[h_emp, h_ep]
        aesop
      | cons h_adj' r => contradiction
    else
      have h_pq_end : q.edges.getLast h_q_nil = p.edges.getLast h_nnil := q.cons_last_edge h_adj h_q_nil
      have : q.edges.head h_q_nil ∉ M.edgeSet := (iff_not_comm.mp (trail_cons_alt_edge h_adj h_q_nil h_alt h_tr)).mp h_fst_match
      have ih := alt_ends_unmatch_match q (IsTrail.of_cons h_tr) (alt_of_cons' h_alt) h_q_nil (h_pq_end ▸ h_lst_match) this
      show p.edgeSet.ncard + 1 = 2*(M.edgeSet ∩ p.edgeSet).ncard
      have : p.edgeSet.ncard = q.edgeSet.ncard + 1 := trail_cons_edgeset_ncard h_tr
      have : (M.edgeSet ∩ p.edgeSet).ncard = (M.edgeSet ∩ q.edgeSet).ncard + 1 := trail_cons_edgeset_inter_ncard_plus h_tr h_fst_match
      omega

end Walk
