module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Source
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.OddClasses

/-!
# The complete native M24 small-degree spectrum

The eight large models, four small models and trivial module saturate the
proved bound of thirteen odd-order conjugacy classes. The resulting absolute
small-degree spectrum is unconditional on the actual Witt-design group.
The earlier presentation and conditional native-realization APIs are retained.

Sources: GM02 Proposition 5.1; Aschbacher–Smith K.4, p.457.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum
open AbsoluteSpectrum AbsoluteSpectrum.LargeModels
open Degrees12421792.NativeActions.Presentation
universe v

/-- Saturation with the proved small models and odd-class bound, for the literal
native large models constructed from presentation injectivity. -/
theorem absoluteSmallSpectrum_of_native_injective
    (hinj : Function.Injective toCarrier) : AbsoluteSmallSpectrum.{v} :=
  absoluteSmallSpectrum_of_models smallModelsExist
    (largeModelsExist_of_native_injective hinj) oddClassBound

/-- Concrete presentation-order consumer, with no residual matrix certificates. -/
theorem absoluteSmallSpectrum_of_presentation_bound
    (h : Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 244823040) :
    AbsoluteSmallSpectrum.{v} :=
  absoluteSmallSpectrum_of_native_injective (toCarrier_injective_of_bound h)

/-- The relaxed bound discharges the native comparison using the proved multiplier. -/
theorem absoluteSmallSpectrum_of_double_bound
    (h : Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 489646080) :
    AbsoluteSmallSpectrum.{v} :=
  absoluteSmallSpectrum_of_native_injective (toCarrier_injective_of_double_bound h)

/-- Actual consumer of the first-four-relator route, retaining its two source obligations. -/
theorem absoluteSmallSpectrum_of_first_and_cover
    (hf : OrderBound.LocalRelations.Mixed.FirstRelation)
    (cover : Subgroup.GeneratorCosetCover OrderBound.boundSubgroup
      OrderBound.generator (Fin 40320)) : AbsoluteSmallSpectrum.{v} :=
  absoluteSmallSpectrum_of_native_injective (toCarrier_injective_of_first_and_cover hf cover)

/-- The spectrum consumer of the native tensor route. The degree-320 pair is
proved; the two largest native realizations remain explicit. -/
theorem absoluteSmallSpectrum_of_native_largest
    (h1242 : Nonempty (Degrees12421792.NativeRealization
      Degrees12421792.Data1242.first Degrees12421792.Data1242.second))
    (h1792 : Nonempty (Degrees12421792.NativeRealization
      Degrees12421792.Data1792.first Degrees12421792.Data1792.second)) :
    AbsoluteSmallSpectrum.{v} :=
  absoluteSmallSpectrum_of_models smallModelsExist
    (largeModelsExist_of_native_largest h1242 h1792) oddClassBound

/-- Exhaustion of the absolute small-degree window on the native group. -/
theorem absoluteSmallSpectrum : AbsoluteSmallSpectrum.{v} :=
  absoluteSmallSpectrum_of_models smallModelsExist largeModelsExist oddClassBound

end Representation.Mathieu.M24DegreeSpectrum
