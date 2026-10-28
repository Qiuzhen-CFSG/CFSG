module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Source

/-!
# The early MS93 distance-four argument

The initial factorization, radius-kernel centrality and edge calculations are
proved in this subtree. The radius-kernel commutator is also proved noncentral
in the full vertex stabilizer. The source midpoint comparison supplies the
moving-kernel transfer under centrality of the radius-derived subgroup.
The selected seed's fixed-quotient calculation supplies edge placement under
failure of the radius-center equality. `DistanceFour.earlyFacts` combines
these proved steps and constructs every field of EarlyFacts from CommonFacts
and b = 4, including derived noncentrality and the radius-center equality.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.1)--(4.6.7), pp.900--904.
-/
