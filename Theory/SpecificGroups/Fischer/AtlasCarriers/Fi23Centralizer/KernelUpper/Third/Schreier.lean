module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Reduction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.InitialSteps
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Schreier.Checker

/-!
# Bitplane certificate assembly for the third Fi23 prefix step

The literal positive Schreier identities follow from two independent numerical
certificates: the twenty signed circuit routes match the published permutations,
and the fixed words agree on all fifteen separating bitplanes. This module
connects those obligations to the actual stabilizer containment. The finite
certificates are explicit premises here; neither the unconditional `steps` nor
the unconditional third stabilizer containment is asserted.

Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u and the Fischer paragraph of
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, near line 1042.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection

namespace KernelUpperThird

/-- Assembly boundary for the circuit-agreement and word-certificate producers. -/
theorem steps_of_bit_certificates (hSecond : Schreier.SecondAgreement)
    (hSigned : Schreier.SignedAgreement) (hBits : ∀ a, Schreier.BitStep a) :
    ∀ a, Step a :=
  fun a => Schreier.step_of_bitStep hSecond hSigned a (hBits a)

end KernelUpperThird

/-- The concrete consumer of the compressed certificates. Generator agreement
with the original cycle-decoded target is retained as an independent premise. -/
theorem third_stabilizer_le_of_bit_certificates
    (hGenerators : ∀ i, KernelUpperThird.packedGenerator i = KernelData.generator i)
    (hSecond : KernelUpperThird.Schreier.SecondAgreement)
    (hSigned : KernelUpperThird.Schreier.SignedAgreement)
    (hBits : ∀ a, KernelUpperThird.Schreier.BitStep a) :
    ∀ p ∈ KernelUpperData.second, p 27 = 27 → p ∈ KernelData.intermediate :=
  third_stabilizer_le_of_certificates hGenerators
    (KernelUpperThird.steps_of_bit_certificates hSecond hSigned hBits)

end Sporadic.Fischer.Fi23.CentralizerSection
