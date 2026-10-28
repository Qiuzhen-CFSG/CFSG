module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.FusionReduction

/-!
# Assembly of a binary involution-coverage certificate

The nine fixed words in `Two/Setup.lean` give 512 binary products. Division
closure and distinctness make their range a subgroup of order 512. A separate
fusion certificate sends every involution in that range to the first standard
generator, which is the representative at index zero. Thus no ambient order
or simplicity assertion is needed for this local argument.

The concrete identities remain explicit hypotheses here until their matrix
certificates are supplied. Word provenance is documented in `Two/source/`.
-/

namespace ONan.Simplicity

/-- Assemble independently checked enumeration and involution fusion. -/
public theorem localPrimeCoverage_two_of_normalForms
    (hclosed : Subgroup.BinaryNormalForm.DivisionClosed TwoCertificate.generators)
    (hinj : Function.Injective TwoCertificate.normalForm)
    (hfusion : ∀ v, orderOf (TwoCertificate.normalForm v) = 2 →
      ∃ g : Model, generatorA = g * TwoCertificate.normalForm v * g⁻¹) :
    LocalPrimeCoverage 2 9 := by
  let H := Subgroup.BinaryNormalForm.subgroup TwoCertificate.generators hclosed
  refine ⟨H, Subgroup.BinaryNormalForm.card_subgroup _ hclosed hinj, ?_⟩
  intro y hy
  obtain ⟨v, hv⟩ := y.property
  have hv' : TwoCertificate.normalForm v = (y : Model) := hv
  have ho : orderOf (TwoCertificate.normalForm v) = 2 := by
    rw [hv', Subgroup.orderOf_coe, hy]
  obtain ⟨g, hg⟩ := hfusion v ho
  refine ⟨0, 1, g, ?_⟩
  change generatorA = g * (y : Model) ^ 1 * g⁻¹
  simpa only [pow_one, hv'] using hg

end ONan.Simplicity
