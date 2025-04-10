import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import Mathlib.Logic.Basic

import LEANGroupProjectBerge.Basic
import LEANGroupProjectBerge.SymDiffEvenCycle

namespace SimpleGraph

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w: V}


namespace Walk

--Placeholder from Josh -> changed brackets around h as failed to synthesize w/o
theorem IfBerge{M:G.Subgraph}(h: M.IsMatching)[Finite V]:
(∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M) → ¬ M.IsMaximumMatching := sorry


--Placeholder for left side of tree
theorem berge_left (M : G.Subgraph): ¬(M.IsMaximumMatching) → ∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M := sorry



theorem BergesTheorem [Finite V] (M : G.Subgraph){h: M.IsMatching}:  M.IsMaximumMatching ↔ ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M :=
  have h1: ¬M.IsMaximumMatching ↔ (∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M) := {
    mp := berge_left M
    mpr := IfBerge h
  }
  have h2: M.IsMaximumMatching ↔ ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M := by aesop
  h2
