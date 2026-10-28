module

public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.Translations

/-!
# Source radical actors and the octad block word calculation

This interface exports the actual radical and even cocode subgroup definitions,
their literal quotient images, the exact block kernel on collected even cocode
words, and the diagonal weights and signed translation coverage on the real
64-dimensional blocks. The only action hypotheses are the three signed-vector
laws of 29.12, packaged as `Radical.GeneratorLaws`.

This is not yet the complete 29.13(2),(4): global radical collection, normality,
the source setwise products, the extraspecial quotient, fixed-space equality,
and identification of the common weight lines still require proofs. The
existing `NOctad` and `LocalStructure` interfaces are preserved.

Source: Aschbacher, *Sporadic Groups*, 14.4–14.5, Section 27, 29.13(2),(4),
and the weight/translation argument in 30.1, printed pp. 60–62, 144, 160–163.
-/
