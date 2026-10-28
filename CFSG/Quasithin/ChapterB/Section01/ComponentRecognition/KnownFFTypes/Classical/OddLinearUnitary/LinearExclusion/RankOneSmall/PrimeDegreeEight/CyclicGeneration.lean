module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.ModelBounds
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.Reduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.InnerSeeds
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.OuterSeeds

/-!
# Small-prime cyclic actor generation

For each of the prime field sizes 13, 17, 19 and 23, four inner conjugates
of any cyclic elementary abelian actor generate a subgroup containing all
inner automorphisms of the actual PSL₂. Explicit matrix words supply both
inner and diagonal outer involution representatives. Involution fusion,
prime-field automorphism coverage and field equivalence transport extend
these configurations to every actor, with conjugators still in PSL₂.

This discharges the cyclic model premise of
`source_degree_eight_of_model_generation`; its independent four-group
premise and the representation-theoretic assembly remain with the consumer.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight

/-- Four PSL₂ conjugates of every cyclic actor contain the inner automorphism
group at the four small prime parameters, including diagonal outer actors. -/
public theorem cyclicModelGeneration : CyclicModelGeneration :=
  CyclicGeneration.cyclicModelGeneration_of_seeds
    CyclicGeneration.innerSeeds CyclicGeneration.outerSeeds

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight
