module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Reduction

/-!
# The degree-twenty Higman--Sims fixed-space calculation

The reduction module provides the actual central-quotient action, elementary
rank bounds, exhaustive marked outer involution cases, and the common-fixed-space
argument for centralizer conjugates. Its conditional assembly applies the three
remaining module calculations to `SourceHypotheses.not_cubicRatio_le_two_of_inputs`.

The inner, elementary outer, and symmetric outer representation estimates remain
separate obligations. No unconditional degree-twenty displacement theorem is
asserted by this module yet.

Source: Guralnick--Malle, *Classification of 2F-modules, I*, Proposition 5.1,
HS paragraph, preprint pp.16--17; Aschbacher--Smith K.4, printed p.457.
-/
