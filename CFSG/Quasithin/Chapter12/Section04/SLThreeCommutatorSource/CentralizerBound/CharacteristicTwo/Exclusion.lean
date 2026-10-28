module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.Index
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.Reduction

/-!
# Exclusion of the characteristic-two hyperplane centralizer

The actual L₃ hyperplane supplies the stabilizer geometry. E.6.7 selects its
literal residual block, and the moved C.5.4–7 calculation proves the local
normalizer has index two. E.6.14 then contradicts the geometric index eight.

Source: Aschbacher–Smith 12.4.8, printed p.815, using E.6.14, p.251.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo
open ChapterE ChapterE.Section06 ChapterE.Section06.InvariantSubspaces
universe u

/-- The characteristic-two case of the original escaping-hyperplane reductio. -/
theorem characteristicTwoExclusion : CharacteristicTwoExclusion.{u} := by
  intro G _ _ T L V U c hc
  exact false_of_inputs c hc c.stabilizer_geometry
    (blockSelection c) (blockIndex c)

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo
end
