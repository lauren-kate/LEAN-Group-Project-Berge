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



theorem deg_zero_isolated {F : SimpleGraph V} (c : F.ConnectedComponent):
    (∃v : V, v ∈ c.supp ∧ (F.neighborSet v).encard = 0) → c.componentAltPath M₁ := by
  intro h
  obtain ⟨v, ⟨h_vc, h_dv0⟩⟩ := h
  let P : F.Walk v v := Walk.nil
  exists v, v, P
  constructor
  · have h_p : P.IsPath := P.isPath_iff_eq_nil.mpr rfl
    exact {
    edges_nodup := h_p.edges_nodup
    support_nodup := h_p.support_nodup
    alternates := by aesop }
  · intro x h_xc
    replace h_dv0 : F.neighborSet v = ∅ := Set.encard_eq_zero.mp h_dv0
    have : F.Reachable v x := by
      simp_all only [ConnectedComponent.mem_supp_iff]
      subst h_xc
      simp_all only [ConnectedComponent.eq]
    apply Nonempty.elim this
    intro Q
    cases Q with
    | nil => exact Walk.mem_support_nil_iff.mpr rfl
    | cons h Q' =>
      rename_i w
      have : w ∈ F.neighborSet v := h
      simp_all only [Set.mem_empty_iff_false]






theorem matching_symm_diff_alt_paths_cycles (hm₁ : M₁.IsMatching) (hm₂ : M₂.IsMatching) :
  ∀c : (symmDiff M₁.spanningCoe M₂.spanningCoe).ConnectedComponent,
  c.componentAltCycle M₁ ∨ c.componentAltPath M₁ := by
    sorry
