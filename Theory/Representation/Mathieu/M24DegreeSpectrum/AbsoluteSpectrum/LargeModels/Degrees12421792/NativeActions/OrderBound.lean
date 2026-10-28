module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalOrder

/-!
# Assembly boundary for the ATLAS M24 presentation bound

The independent nine-relator local presentation is finite of order at most
6072. To apply it to the literal subgroup of the original seven-relator group,
the remaining local relations must be proved there. A second, independent
input is a certified cover by 40320 cosets. This module combines exactly those
inputs and then applies the existing marked surjection to the native carrier.

Neither outstanding input is asserted. In particular this module does not
export the unconditional `presentation_bound` until both are discharged.

Source: John Bray, ATLAS M24G1-P1; subgroup program M24G1-max8W1.
See `OrderBound/source/README.md` for the completed local certificate.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
open Subgroup.CosetWordCertificate

/-- The remaining two independent mathematical inputs imply the requested bound. -/
theorem presentation_bound_of_cover_and_relations
    (hrel : ∀ i, eval OrderBound.boundGenerator (OrderBound.localRelatorLetters i) = 1)
    (cover : Subgroup.GeneratorCosetCover OrderBound.boundSubgroup
      OrderBound.generator (Fin 40320)) :
    Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 244823040 := by
  obtain ⟨hf, hc⟩ := OrderBound.boundSubgroup_finite_card_le hrel
  let : Finite OrderBound.boundSubgroup := hf
  obtain ⟨hf', hc'⟩ := cover.finite_card_le (PresentedGroup.closure_range_of relators)
  refine ⟨hf', hc'.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 40320 hc

/-- Actual native comparison consumer, retaining both missing source obligations. -/
theorem toCarrier_injective_of_cover_and_relations
    (hrel : ∀ i, eval OrderBound.boundGenerator (OrderBound.localRelatorLetters i) = 1)
    (cover : Subgroup.GeneratorCosetCover OrderBound.boundSubgroup
      OrderBound.generator (Fin 40320)) :
    Function.Injective toCarrier :=
  toCarrier_injective_of_bound (presentation_bound_of_cover_and_relations hrel cover)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
