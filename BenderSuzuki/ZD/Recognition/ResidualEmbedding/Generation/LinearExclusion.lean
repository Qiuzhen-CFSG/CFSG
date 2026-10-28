module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Basic

/-!
# Assembly boundary for exclusion of the proper linear case

Proposition 15.1 of GLS, Volume 4, Chapter 2 excludes an actual isomorphism
`L ≃* PSL₂(2^n)` for the proper group `L = ⟨z,t,[O_{2′}(D),t]⟩`.

`LinearExclusion.Basic` establishes two elementary local consequences and
the final focal-transfer contradiction. The remaining source analysis must
construct the normal complement to `D` in `M` and prove `O²(D) < D` from
the supplied linear model. The lemmas already exported here are conditional
at precisely those local premises; they do not assert Proposition 15.1.

The unconditional `proper_residualGenerated_linear_false` remains to be
assembled in this module after the local source arguments are proved.
-/
