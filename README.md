# LEAN-Group-Project-Berge

The statement of Berge's theorem and its proof are contained within the file Berge.lean. It requires imports from OnlyIf.lean and LocateAugPath to form the proof.

Berge.lean ---- contains the proof of Berge's theorem
Basic.lean ---- Contains definitions of Maximal and Maximum Matchings
Contains most of the structures defined, including Alternating and Augmenting paths, as well as Components
Also contains some basic theorems used throughout the theorems, on paths and connected components that weren't included in Mathlib



# fill in your own!

OnlyIf.lean ---- contains proof of the only if direction, that there exists an M-augmenting path implies that M is not maximum
Also includes some simple lemmas about finiteness of graphs

AugPathNeighbours.lean ---- Contains part of the proof that the Symmetric Difference of M and an M-augmenting path is a matching, every vertex along the augmenting path has a unique neighbour in this new graph