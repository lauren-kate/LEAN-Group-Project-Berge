
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import LEANGroupProjectBerge.Basic

namespace SimpleGraph


universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M₁ : G.Subgraph}
variable {M₂ : G.Subgraph}




lemma gt_nonempty {α : Type u} {s : Set α} {n : ℕ∞} (h : s.encard > n) : s.Nonempty := by
  cases n with
  | coe n' =>
    cases n' with
    | zero => exact Set.encard_pos.mp h
    | succ m =>
      have : @Nat.cast ℕ∞ _ (m+1) > 0 := by aesop
      have h' : s.encard > 0 := gt_trans h this
      exact Set.encard_pos.mp h'
  | top =>
    have : ¬s.encard > ⊤ := not_top_lt
    contradiction


lemma gt_succ {α : Type u} {s : Set α} {k : ℕ} (h : s.encard + 1 > ↑(Nat.succ k)) : s.encard > k := by
  match @exists_eq ℕ∞ s.encard with
  | ⟨ c, h_c_eq ⟩ =>
    cases c with
    | coe n =>
      rw [←h_c_eq]; rw [←h_c_eq] at h
      simp at h
      have : k+1 < n+1 := ENat.coe_lt_coe.mp h
      exact ENat.coe_lt_coe.mpr (Nat.add_one_lt_add_one_iff.mp this)
    | top =>
      rw [←h_c_eq]
      exact ENat.coe_lt_top k


lemma set_three_uq {α : Type u} {s : Set α} (h : s.encard > 2) :
  ∃ (a b c : α), a∈s ∧ b∈s ∧ c∈s ∧ a≠b ∧ a≠c ∧ b≠c := by
  have s_nempty: s.Nonempty := gt_nonempty h
  match s_nempty with
  | ⟨ a, h_a_smem ⟩ =>
    rw [←Set.encard_diff_singleton_add_one h_a_smem] at h
    have h_card₁: (s \ {a}).encard > 1 := gt_succ h
    have sma_nempty : (s \ {a}).Nonempty := gt_nonempty h_card₁
    match sma_nempty with
    | ⟨ b, h_b_mem ⟩ =>
      rw [←Set.encard_diff_singleton_add_one h_b_mem] at h_card₁
      have h_card₂: ((s \ {a}) \ {b}).encard > 0 := gt_succ h_card₁
      have smab_nempty : ((s \ {a}) \ {b}).Nonempty := gt_nonempty h_card₂
      match smab_nempty with
      | ⟨ c, h_c_mem ⟩ =>
        exact ⟨ a, b, c, ⟨h_a_smem, by aesop, by aesop, by aesop, by aesop, by aesop ⟩ ⟩



lemma edge_verts {M : G.Subgraph} {u v : V} (h : M.Adj u v) : u ∈ M.verts := by
  apply @Subgraph.mem_verts_of_mem_edge _ _ _ s(u,v) u
  · exact Subgraph.mem_edgeSet.mpr h
  · aesop


lemma matching_contr (hm : M₁.IsMatching) {a b c : V} (hne : a≠b) (h : M₁.Adj c a) (h' : M₁.Adj c b) : False := by
  match hm (edge_verts h) with
  | ⟨ x, h_x ⟩ =>
    have : a=x := h_x.2 a h
    have : b=x := h_x.2 b h'
    exact hne (by aesop)


theorem matching_symm_diff_dg_lt2 (hm₁ : M₁.IsMatching) (hm₂ : M₂.IsMatching) :
  ∀v : V, ((symmDiff M₁.spanningCoe M₂.spanningCoe).neighborSet v).encard <= 2 := by
  intro v
  let F := (symmDiff M₁.spanningCoe M₂.spanningCoe)
  show (F.neighborSet v).encard ≤ 2
  by_contra h'
  match set_three_uq (lt_of_not_ge h') with
  | ⟨ a, b, c, ⟨h_amem, h_bmem, h_cmem, h_aneb, h_anec, h_bnec ⟩ ⟩ =>
    have h_va : F.Adj v a := (F.mem_neighborSet v a).mp h_amem
    have h_vb : F.Adj v b := (F.mem_neighborSet v b).mp h_bmem
    have h_vc : F.Adj v c := (F.mem_neighborSet v c).mp h_cmem
    unfold F at h_va
    unfold symmDiff at h_va
    cases h_va with
    | inl h₁a =>
      cases h_vb with
      | inl h₁b =>
        exact matching_contr hm₁ h_aneb h₁a.1 h₁b.1
      | inr h₂b =>
        cases h_vc with
        | inl h₁c =>
          exact matching_contr hm₁ h_anec h₁a.1 h₁c.1
        | inr h₂c =>
          exact matching_contr hm₂ h_bnec h₂b.1 h₂c.1
    | inr h₂a =>
      cases h_vb with
      | inl h₁b =>
        cases h_vc with
        | inl h₁c =>
          exact matching_contr hm₁ h_bnec h₁b.1 h₁c.1
        | inr h₂c =>
          exact matching_contr hm₂ h_anec h₂a.1 h₂c.1
      | inr h₂b =>
        exact matching_contr hm₂ h_aneb h₂a.1 h₂b.1





namespace ConnectedComponent

def componentAltCycle {F : SimpleGraph V} (c : F.ConnectedComponent) (M : G.Subgraph) : Prop :=
  ∃ (u : V) (p : F.Walk u u), p.IsAlternatingCycle M ∧ ∀x:V, x ∈ c.supp → x ∈ p.support


def componentAltPath {F : SimpleGraph V} (c : F.ConnectedComponent) (M : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : F.Walk u v), p.IsAlternatingPath M ∧ ∀x:V, x ∈ c.supp → x ∈ p.support

end ConnectedComponent


theorem matching_symm_diff_alt_paths_cycles (hm₁ : M₁.IsMatching) (hm₂ : M₂.IsMatching) :
  ∀c : (symmDiff M₁.spanningCoe M₂.spanningCoe).ConnectedComponent,
  c.componentAltCycle M₁ ∨ c.componentAltPath M₁ := by
    sorry






lemma alt_of_cons {u v w : V} {F : SimpleGraph V} {h : F.Adj u v} {p : F.Walk v w} :
    (Walk.cons h p).IsAlternatingPath M₁ → p.IsAlternatingPath M₁ := by
  intro h_alt
  constructor
  · exact h_alt.of_cons
  · intros x y z h_xnez h_xy h_yz
    let p' := Walk.cons h p
    have h_xyp' : s(x,y) ∈ p'.edges := by aesop
    have h_yzp' : s(y,z) ∈ p'.edges := by aesop
    exact h_alt.alternates h_xnez h_xyp' h_yzp'



lemma aug_card {u v : V} {F : SimpleGraph V} (p : F.Walk u v) (hm : M₁.IsMatching) :
    u≠v → v ∉ M₁.support → p.IsAlternatingPath M₁ →
    (M₁.Adj u (p.getVert 1) → p.toSubgraph.edgeSet.encard = 2*(M₁.edgeSet ∩ p.toSubgraph.edgeSet).encard )
    ∧ (¬M₁.Adj u (p.getVert 1) → p.toSubgraph.edgeSet.encard = 2*(M₁.edgeSet ∩ p.toSubgraph.edgeSet).encard + 1) := by
  induction p with
  | nil =>
    intros
    contradiction
  | cons h_adj p' ih =>
    rename_i u w v
    intros h_unv h_vunsat h_consalt
    have h_p'alt : p'.IsAlternatingPath M₁ := alt_of_cons h_consalt
    let p := Walk.cons h_adj p'
    let EP := p.toSubgraph.edgeSet
    let EPnM := M₁.edgeSet ∩ p.toSubgraph.edgeSet
    apply And.intro
    · show M₁.Adj u (p.getVert 1) → EP.encard = 2*EPnM.encard
      intro h_endmatch
      match em (w=v) with
      | Or.inl h_eq =>
        have : p.getVert 1 = v := by aesop
        rw [this] at h_endmatch
        have : v∈ M₁.support := M₁.mem_support.mpr ⟨u, M₁.adj_symm h_endmatch⟩
        contradiction
      | Or.inr h_neq =>
        let EP' := p'.toSubgraph.edgeSet
        let EP'nM := M₁.edgeSet ∩ p'.toSubgraph.edgeSet
        have : (M₁.Adj w (p'.getVert 1) → EP'.encard = 2 * EP'nM.encard) ∧
                (¬M₁.Adj w (p'.getVert 1) → EP'.encard = 2 * EP'nM.encard + 1) :=
                ih h_neq h_vunsat h_p'alt
        sorry
    · show ¬M₁.Adj u (p.getVert 1) → EP.encard = 2*EPnM.encard + 1
      intro h_uunsat
      sorry




theorem aug_symm_diff_gt {u v : V} {M : G.Subgraph} {p : G.Walk u v} (h : p.IsAugmentingPath M) :
  (symmDiff M.spanningCoe p.toSubgraph.spanningCoe).edgeSet.ncard > M.edgeSet.ncard := by
  let F := (symmDiff M.spanningCoe p.toSubgraph.spanningCoe)
  show F.edgeSet.ncard > M.edgeSet.ncard
  sorry
