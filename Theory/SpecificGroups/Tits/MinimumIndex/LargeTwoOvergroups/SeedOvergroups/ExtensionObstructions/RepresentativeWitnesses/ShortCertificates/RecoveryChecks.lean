module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.Contracts
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.MoveChecks
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.CoverageContracts
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.CoverageLow
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.CoverageMiddle
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.CoverageHigh
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.Pilot.Seed000

/-!
# Recoveries from certified generator walks

All 122 compact transition tables are sound: each transition constructs an
actual left seed factor. Composition along the original normal form therefore
turns numeric coverage into the exact recovery certificate. The three checked
coverage ranges exhaust all 122 seeds and give `recoveryCertificates` with
no extra hypothesis.

The catalogue order premise is independent and appears only in the final
representative application. No seed order, placement geometry, or exhaustive
seed classification is used. Source: Parrott (1972), section 5, p.683;
`RecoveryChecks/source/README.md` and the parent source READMEs.
-/

public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates

/-- Only the finite coverage premise remains; every generator move is proved. -/
theorem recoveryCertificates_of_numericCoverage (h : RecoveryAction.NumericCoverage) :
    RecoveryCertificates :=
  RecoveryAction.recoveryCertificates_of_coverage RecoveryAction.stepData
    RecoveryAction.moveSound h

/-- Assembly boundary for three independent finite ranges. -/
theorem recoveryCertificates_of_coverageRanges
    (h₀ : RecoveryAction.CoverageOn 0 40) (h₁ : RecoveryAction.CoverageOn 40 40)
    (h₂ : RecoveryAction.CoverageOn 80 42) : RecoveryCertificates :=
  recoveryCertificates_of_numericCoverage (RecoveryAction.numericCoverage_of_ranges h₀ h₁ h₂)

/-- Every original short case has an actual seed member and recovery equation. -/
theorem recoveryCertificates : RecoveryCertificates :=
  recoveryCertificates_of_coverageRanges RecoveryAction.numericCoverageLow
    RecoveryAction.numericCoverageMiddle RecoveryAction.numericCoverageHigh

/-- The recovery premise of the short representative branch is discharged;
only the independent catalogue-order certificate remains. -/
theorem representativeWitnesses_of_orderCertificates (ho : OrderCertificates)
    (i : Fin 122) (a b : Fin 32) (c : Fin 15) (hs : witnessCase i a b c = .short) :
    RepresentativeWitness i a b (shortIndex c) := by
  obtain ⟨q, n, h⟩ := recoveryCertificates i a b c hs
  exact representativeWitness_of_certificate i a b c q n h (ho n c h.2.1)

/-- All 14,704 short cases for the literal seed zero, with no extra premise. -/
theorem seedZeroRecoveryCertificates (a b : Fin 32) (c : Fin 15)
    (hs : witnessCase 0 a b c = .short) :
    ∃ q n : Fin 2048, RecoveryCertificate 0 a b c q n := by
  obtain ⟨n, hn, hw⟩ := RecoveryAction.coverage000 a b c hs
  obtain ⟨q, hq⟩ := RecoveryAction.recovery_of_walk 0 RecoveryAction.stepData000
    RecoveryAction.moveSound000 a b c n hn hw
  exact ⟨q, n, hq⟩

/-- Literal representative application of the complete seed-zero family. -/
theorem seedZeroRepresentativeWitnesses (ho : OrderCertificates)
    (a b : Fin 32) (c : Fin 15) (hs : witnessCase 0 a b c = .short) :
    RepresentativeWitness 0 a b (shortIndex c) := by
  obtain ⟨q, n, h⟩ := seedZeroRecoveryCertificates a b c hs
  exact representativeWitness_of_certificate 0 a b c q n h (ho n c h.2.1)

/-- The original representative consumer, with both independent inputs explicit. -/
theorem representativeWitnesses_of_numericCoverage
    (h : RecoveryAction.NumericCoverage) (ho : OrderCertificates)
    (i : Fin 122) (a b : Fin 32) (c : Fin 15) (hs : witnessCase i a b c = .short) :
    RepresentativeWitness i a b (shortIndex c) := by
  obtain ⟨q, n, hr⟩ := recoveryCertificates_of_numericCoverage h i a b c hs
  exact representativeWitness_of_certificate i a b c q n hr (ho n c hr.2.1)

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates
