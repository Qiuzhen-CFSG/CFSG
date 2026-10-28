module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.InnerSeeds
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.Reduction

/-!
# Discharging the inner premise of small-prime cyclic generation

The unconditional `innerSeeds` construction discharges the inner-involution
premise of the existing representative-to-actor reduction, with the actual
PSL₂ conjugators and quotient conventions. The outer seed construction remains
an explicit premise for the parent cyclic-model assembly.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration

/-- Only the diagonal outer configurations remain in the cyclic-model reduction. -/
public theorem cyclicModelGeneration_of_outerSeeds (houter : OuterSeeds) :
    CyclicModelGeneration :=
  cyclicModelGeneration_of_seeds innerSeeds houter

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration
