import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

import LEANGroupProjectBerge.Basic



namespace SimpleGraph

universe u
variable {V : Type u}
variable {G : SimpleGraph V}
variable {M : G.Subgraph}
variable {u v w x: V}

open Walk


lemma symmDiffIsMatching (M : G.Subgraph) (u v : V ) (p: G.Walk u v) (h1: M.IsMatching) (h2: p.IsAugmenting M): (symmDiff M p.toSubgraph).IsMatching :=
sorry
