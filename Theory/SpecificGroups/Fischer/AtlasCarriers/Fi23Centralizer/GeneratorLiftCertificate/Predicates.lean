module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.Check
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GeneratorMaps

/-!
# Exact numerical obligations for the Fi23 generator lifts

The word evaluator follows the literal left-action multiplication in
`FixedPointSetup`. The candidate-table check and commutation checks use all
31671 letters. The coordinate check includes the additional `none` point.
Source: GLS3 Table 5.3u and the unchanged ATLAS permutation tables.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate
open Fi24Prime.Fi23Lift.Certificate (sourceA sourceB)

def evalWord (x : Fin 31671) : Fin 31671 :=
  sourceA (sourceB (sourceB (sourceA (sourceB (sourceB (sourceA (sourceB
    (sourceA (sourceB (sourceA (sourceB x)))))))))))

abbrev wordCheck (x : Fin 31671) : Prop := wordMap x = evalWord x

abbrev candidateCheck (x : Fin 31671) : Prop :=
  candidateMap x = (wordMap^[7]) x ∧
  candidateMap (liftA x) = liftA (candidateMap x) ∧
  candidateMap (liftB x) = liftB (candidateMap x)

abbrev actionCheck (i : Fin 3511) : Prop :=
  liftA (ImageData.point (finSuccEquivLast i)) =
    ImageData.point (Option.map Fi22.KernelCertificate.fastA (finSuccEquivLast i)) ∧
  liftB (ImageData.point (finSuccEquivLast i)) =
    ImageData.point (Option.map Fi22.KernelCertificate.fastB (finSuccEquivLast i))

end Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate
