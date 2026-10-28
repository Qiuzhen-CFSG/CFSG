module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.SourceAssembly

/-!
# The local dihedral geometry in Held's Lemma 5.4

Conjugation by tau-prime identifies the literal intersection
`C_G(pi*mu) ∩ C_G(uv)` with a cubic centralizer in `C_G(mu)`. The marked
mu-centralizer model and the calculations for both cubic cycle types provide
actual product coordinates `C3 × C_A7((01)(23))`. They give intersection
order 72 and a dihedral subgroup of order eight. Its normalizer fixes the
central involution, proving Sylow maximality in the full root centralizer.

The central order-three quotient preserves that Sylow group. Exact
centralizer descent identifies the full centralizer of the image of pi*mu
with `C_A7((01)(23))`. `local_geometry` assembles all three conclusions from
the corrected six-point data and the supplied mu-centralizer order.
`local_geometry_of_source` retains the finite simple and nonfusion hypotheses
of the surrounding source argument. Neither result assumes the odd-core
calculation, quotient recognition, or a root factor.

The earlier conditional reductions remain publicly available.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/
