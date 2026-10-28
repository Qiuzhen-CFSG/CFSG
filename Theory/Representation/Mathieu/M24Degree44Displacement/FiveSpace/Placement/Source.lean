module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Placement.Consumer
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Placement.BinaryModels
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.ExteriorBound
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Source
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.OddClasses

/-!
# The universal native M24 order-five fixed-space bound

The complete native large-model family supplies the missing completeness
input for placement into the binary Golay sections. The proved exterior
calculation then gives the unconditional fixed-space bound. The earlier
conditional APIs are retained with their original statements.

Sources: GM02 Proposition 5.1; Aschbacher–Smith K.4, p.457.
-/

public section
namespace Representation.MathieuM24Degree44
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
open LargeModels Degrees12421792.NativeActions.Presentation
universe v

/-- Apply the literal binary section models and the proved exterior calculation
after constructing the native large models. -/
theorem fiveFixedSpaceBound_of_native_injective
    (hinj : Function.Injective toCarrier) : FiveFixedSpaceBound.{v} :=
  fiveFixedSpaceBound_of_binary_section_models FiveSpace.Placement.binarySectionModels
    (largeModelsExist_of_native_injective hinj) oddClassBound
    FiveSpace.golayExteriorFiveBound

/-- The same abstract finite bound supplies both spectrum and displacement inputs. -/
theorem fiveFixedSpaceBound_of_presentation_bound
    (h : Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 244823040) :
    FiveFixedSpaceBound.{v} :=
  fiveFixedSpaceBound_of_native_injective (toCarrier_injective_of_bound h)

/-- The relaxed bound discharges the native comparison using the proved multiplier. -/
theorem fiveFixedSpaceBound_of_double_bound
    (h : Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 489646080) :
    FiveFixedSpaceBound.{v} :=
  fiveFixedSpaceBound_of_native_injective (toCarrier_injective_of_double_bound h)

/-- Actual consumer of the first-four-relator route, retaining its two source obligations. -/
theorem fiveFixedSpaceBound_of_first_and_cover
    (hf : OrderBound.LocalRelations.Mixed.FirstRelation)
    (cover : Subgroup.GeneratorCosetCover OrderBound.boundSubgroup
      OrderBound.generator (Fin 40320)) : FiveFixedSpaceBound.{v} :=
  fiveFixedSpaceBound_of_native_injective (toCarrier_injective_of_first_and_cover hf cover)

/-- Universal placement and the literal exterior bound consume the native
320 pair; only the two largest native realizations remain explicit. -/
theorem fiveFixedSpaceBound_of_native_largest
    (h1242 : Nonempty (Degrees12421792.NativeRealization
      Degrees12421792.Data1242.first Degrees12421792.Data1242.second))
    (h1792 : Nonempty (Degrees12421792.NativeRealization
      Degrees12421792.Data1792.first Degrees12421792.Data1792.second)) :
    FiveFixedSpaceBound.{v} :=
  fiveFixedSpaceBound_of_binary_section_models FiveSpace.Placement.binarySectionModels
    (largeModelsExist_of_native_largest h1242 h1792) oddClassBound
    FiveSpace.golayExteriorFiveBound

/-- Universal placement and the exterior calculation, with all model
construction and class-count premises discharged. -/
theorem fiveFixedSpaceBound : FiveFixedSpaceBound.{v} :=
  fiveFixedSpaceBound_of_binary_section_models FiveSpace.Placement.binarySectionModels
    largeModelsExist oddClassBound FiveSpace.golayExteriorFiveBound

end Representation.MathieuM24Degree44
