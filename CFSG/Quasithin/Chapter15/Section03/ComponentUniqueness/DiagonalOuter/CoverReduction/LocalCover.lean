module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Assembly
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.CenterReduction

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceAssembly

/-!
# The first local-cover reduction for 15.3.38

`local_cover_of_rank_two` selects the diagonal branch from the genuine rank-two
setup and the uniformly quantified earlier alternatives. It constructs a
marking of L/O₂(L) by PSL₃(4), with the actual cubic action, compatible plane
labels and interchange, Z(L)=O₂(L), Z(L)=C_S(L)=C_I(L)=W₁ in the ambient group,
Y₊=Y, Y/O₂(Y)≃E₉, O₂(Y)=S∩L, and the literal products Y=Y_L Y_D and I=L Y_D S.
Normality of L is relative to I. The marked variant retains exactly the
supplied coefficient field, quotient equivalence and original cubic actor.

The earlier `PreGeometry.Source.center_control_of_marked_source` is available
through its narrow module before the component-kernel argument. It constructs
the Borel planes and residuals using image generation, then discharges the
projective root calculations and central-kernel lifting. It has no full
15.3.37 product or arbitrary-automorphism-coverage premise. The later I-product
uses the proved outer-order bound and the actual Sylow and cubic images.

All previous conditional APIs are preserved. The exact earlier source
conclusions remain explicit inputs of this reusable first-paragraph reduction;
subsequent normalizer, transfer and contradiction assembly remains with the
CoverReduction consumer. This module does not assert the whole of 15.3.38.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed pp.1135--1136, through I=L Y_D S.
-/
