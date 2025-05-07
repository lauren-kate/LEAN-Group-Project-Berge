/-
Copyright (c) 2025 Oscar Bryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oscar Bryan, Reuben Brown, Spraeha Jha, A. Basak Kaya, Joshua Render, Lauren Kate Thompson
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import Mathlib.Logic.Basic
import Mathlib.Data.Set.Card

import LEANGroupProjectBerge.Basic
import LEANGroupProjectBerge.LocateAugPath
import LEANGroupProjectBerge.OnlyIf

namespace SimpleGraph

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M M': G.Subgraph}
variable {u v w: V}


namespace Walk



theorem BergesTheorem [Finite V] (M : G.Subgraph){h: M.IsMatching}:  M.IsMaximumMatching ↔ ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M :=
  have h1: ¬M.IsMaximumMatching ↔ (∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M) := {
    mp := matching_not_max_aug h
    mpr := Subgraph.IfBerge h
  }
  have h2: M.IsMaximumMatching ↔ ¬∃ u v: V, ∃ p: G.Walk u v, p.IsAugmentingPath M := by aesop
  h2
