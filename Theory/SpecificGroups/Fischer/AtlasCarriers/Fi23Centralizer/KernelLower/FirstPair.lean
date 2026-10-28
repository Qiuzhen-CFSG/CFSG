module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.First.Initial
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.Second.Reduction

/-!
# Assembly of the first two Fi23 suffix steps

The representatives, inverse index maps, subgroup fixation, word membership,
and defining tree transitions are proved. This assembly leaves the remaining
all-letter transitions explicit, together with the independently owned
comparison of the seven packed inputs with the literal `KernelData` generators.
It does not claim the unconditional first-pair bound until these are discharged.
Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u and the Fischer paragraph near
line 1042 in `refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection
open KernelLowerFirstPair

/-- First suffix point, with only the all-letter positive equations outstanding. -/
theorem packed_first_suffix_le_of_steps (h : ∀ a, First.Step a)
    (p : Equiv.Perm (Fin 31671)) (hp : p ∈ KernelUpperThird.packedSubgroup)
    (h40 : p 40 = 40) : p ∈ afterOne :=
  (First.reduction h).mem_next hp h40

/-- Second suffix point in the literal four-generator intermediate closure. -/
theorem afterOne_second_suffix_le_of_steps (h : ∀ a, Second.Step a)
    (p : Equiv.Perm (Fin 31671)) (hp : p ∈ afterOne)
    (h46 : p 46 = 46) : p ∈ KernelLowerData.afterTwo :=
  (Second.reduction h).mem_next hp h46

/-- The exact consumer contract, conditional only on the three unproved
certificate families. The final assembly owner must discharge each premise. -/
theorem first_pair_stabilizer_le_of_certificates
    (hGenerators : ∀ i, KernelUpperThird.packedGenerator i = KernelData.generator i)
    (hFirst : ∀ a, First.Step a) (hSecond : ∀ a, Second.Step a) :
    ∀ p ∈ KernelData.intermediate,
      p 40 = 40 → p 46 = 46 → p ∈ KernelLowerData.afterTwo := by
  intro p hp h40 h46
  have he : KernelUpperThird.packedGenerator = KernelData.generator := funext hGenerators
  have hp' : p ∈ KernelUpperThird.packedSubgroup := by
    simpa only [KernelUpperThird.packedSubgroup, KernelData.intermediate, he] using hp
  exact afterOne_second_suffix_le_of_steps hSecond p
    (packed_first_suffix_le_of_steps hFirst p hp' h40) h46

end Sporadic.Fischer.Fi23.CentralizerSection
