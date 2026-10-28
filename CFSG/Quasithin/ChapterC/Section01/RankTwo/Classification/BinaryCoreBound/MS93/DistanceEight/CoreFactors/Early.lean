module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Statements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Moving
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Intersections.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Numerical

/-!
# Early orbit-layer calculations for MS93 (4.5)

The actual preceding (4.4) inputs give moving-span containment at every
interior even center of the extended path, a moving span at any M-vertex,
and the numerical bound |H_a| <= 4. Moving/edge generation gives
[V_a,V_(a+4)] <= H_a cap H_(a+4), and a neighboring critical window makes
this commutator nontrivial.

The exact intersection and quotient-centralizer identities, the second-layer
product, |H_a| = 4, and (4.5.2)--(4.5.3) remain source proof obligations.
Their literal output contracts are exported for the two remaining proof
families. This entry point does not assert their existence or the full lemma.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.895--898.
-/
