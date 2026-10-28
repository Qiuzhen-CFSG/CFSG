module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalBasic
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding
public import BenderSuzuki.ZD.Recognition.MinimalReduction.CoverReduction

/-!
# The minimal-counterexample reduction for Theorem ZD

The subgroup and quotient induction steps and the rank-one local embedding
case are proved in `LocalBasic`. `LocalEmbedding` proves the full local
embedding clause from minimality and the absence of nontrivial solvable normal
subgroups. `CoverReduction` assembles generation, conjugacy, fusion, radical
elimination, local embedding and simplicity from the precise double-cover
Sylow-fixer theorem. Odd-core elimination needs no additional input. The
covering theorem remains to be supplied before the unconditional
`SimpleReduction` is asserted.
-/
