module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.Contracts

/-!
# Actual representative applications of the shared arithmetic

Four widely separated seeds exercise the certified normal-form multiplication,
positive-word membership, catalogue lookup and order check. In each case the
conclusion is an actual representative witness in the literal extension, and
the published selector puts the candidate in the short branch.

These are samples, not the complete finite recovery or order families.
Source: Parrott (1972), section 5, p.683; the parent recovery JSON and catalogue.
-/

public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates

private theorem sampleRecoveryZero : RecoveryCertificate 0 0 0 14 16 16 := by
  refine ⟨normalForm_mem_of_word 0 16 [16] ?_ ?_, ?_, ?_⟩
  · intro m hm
    have he := List.mem_singleton.mp hm
    subst m
    decide +kernel
  all_goals decide +kernel

private theorem sampleRecovery31 : RecoveryCertificate 31 31 17 4 8 95 := by
  refine ⟨normalForm_mem_of_word 31 8 [8] ?_ ?_, ?_, ?_⟩
  · intro m hm
    have he := List.mem_singleton.mp hm
    subst m
    decide +kernel
  all_goals decide +kernel

private theorem sampleRecovery63 : RecoveryCertificate 63 17 31 9 74 684 := by
  refine ⟨normalForm_mem_of_word 63 74 [65, 11] ?_ ?_, ?_, ?_⟩
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · decide +kernel
    · have he := List.mem_singleton.mp hm
      subst m
      decide +kernel
  all_goals decide +kernel

private theorem sampleRecoveryLast : RecoveryCertificate 121 31 31 14 90 90 := by
  refine ⟨normalForm_mem_of_word 121 90 [65, 27] ?_ ?_, ?_, ?_⟩
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · decide +kernel
    · have he := List.mem_singleton.mp hm
      subst m
      decide +kernel
  all_goals decide +kernel

theorem sampleWitnessZero :
    witnessCase 0 0 0 14 = .short ∧ RepresentativeWitness 0 0 0 17 := by
  refine ⟨by decide +kernel, representativeWitness_of_certificate 0 0 0 14 16 16
    sampleRecoveryZero (orderTest_sound 16 17 ?_)⟩
  decide +kernel

theorem sampleWitness31 :
    witnessCase 31 31 17 4 = .short ∧ RepresentativeWitness 31 31 17 7 := by
  refine ⟨by decide +kernel, representativeWitness_of_certificate 31 31 17 4 8 95
    sampleRecovery31 (orderTest_sound 95 7 ?_)⟩
  decide +kernel

theorem sampleWitness63 :
    witnessCase 63 17 31 9 = .short ∧ RepresentativeWitness 63 17 31 12 := by
  refine ⟨by decide +kernel, representativeWitness_of_certificate 63 17 31 9 74 684
    sampleRecovery63 (orderTest_sound 684 12 ?_)⟩
  decide +kernel

theorem sampleWitnessLast :
    witnessCase 121 31 31 14 = .short ∧ RepresentativeWitness 121 31 31 17 := by
  refine ⟨by decide +kernel, representativeWitness_of_certificate 121 31 31 14 90 90
    sampleRecoveryLast (orderTest_sound 90 17 ?_)⟩
  decide +kernel

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates
