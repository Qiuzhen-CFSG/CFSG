module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceGreaterFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.OriginalInput

/-!
# Source center bounds for the binary numerical theorem

The distance-four branch constructs the actual cover of two natural modules
and proves that the center of the commutator core has order at most 32.
Its application preserves the original core through InputSetup.coreEquiv.
For the larger-distance branch, the conditional numerical assembly uses only
containment of the core center in U join H and the upper bound |H| <= 4.
Genuine local centrality and moving-span generation suffice for that H bound.
The one-sided center containment and those earlier source inputs remain to
be constructed; the conditional assembly does not assert the full branch.

The original-input assembly now constructs the abelian alternative, source
realization, common/radius facts and distance split. Its sole callback asks
for the two larger-distance estimates on the actual source setup. The enclosing
assembly must discharge that callback to obtain the unconditional numerical
disjunction. No exact-U kernel equality or elementary-center model is required.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.6), and Aschbacher--Smith,
C.1.31--34, printed pp.135--137 (combined manuscript, 1 March 2004).
-/
