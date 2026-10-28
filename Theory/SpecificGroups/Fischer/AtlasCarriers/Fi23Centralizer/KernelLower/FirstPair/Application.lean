module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower

/-!
# First-pair certificates in the seven-point assembly

This actual application discharges the first-pair premise of
`intermediate_four_point_bound_of_steps` from the three explicit certificates.
The remaining pair and terminal certificates stay with their existing owners.
This conditional theorem is not the GLS3 Table 5.3u source result.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection
open KernelLowerFirstPair KernelLowerData

theorem intermediate_four_point_bound_of_first_pair_certificates
    (hGenerators : ∀ i, KernelUpperThird.packedGenerator i = KernelData.generator i)
    (hFirst : ∀ a, First.Step a) (hSecond : ∀ a, Second.Step a)
    (hnext : ∀ p ∈ afterTwo, p 63 = 63 → p 66 = 66 → p ∈ afterFour)
    (p : Equiv.Perm (Fin 31671)) (hp : p ∈ KernelData.intermediate)
    (h40 : p 40 = 40) (h46 : p 46 = 46) (h63 : p 63 = 63) (h66 : p 66 = 66) :
    p ∈ afterFour :=
  intermediate_four_point_bound_of_steps
    (first_pair_stabilizer_le_of_certificates hGenerators hFirst hSecond)
    hnext p hp h40 h46 h63 h66

end Sporadic.Fischer.Fi23.CentralizerSection
