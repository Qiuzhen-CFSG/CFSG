module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Certificates

/-!
# A complete seed-zero extension certificate

The saved exploratory word is the normal form 30. Its product with the
seventeenth double-coset word has order thirteen. The recovery equality and
membership in the literal seed are both checked, so this supplies the exact
representative witness, including the actual order and extension membership.
Source: Parrott (1972), section 5, p.683; `source/README.md`.
-/

public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates

/-- The saved seed-zero pilot, now a witness in the literal extension. -/
theorem pilotWitness : RepresentativeWitness 0 0 0 17 := by
  apply representativeWitness_of_tests 0 0 0 17 30 [16,64,4,1,64,1,1]
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- A two-occurrence certificate for a candidate without a short witness. -/
theorem productPilotWitness : RepresentativeWitness 0 0 17 11 := by
  apply representativeWitness_of_productTests 0 0 17 11
    [(2010, [64,16,4,4,1]), (1663, [4,2,1])]
  · decide +kernel
  · decide +kernel
  · decide +kernel

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates
