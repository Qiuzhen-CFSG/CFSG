module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.Data

/-!
# Independent finite coverage ranges

The compact generator actions reduce the remaining work to catalogue entries
whose computed walk has the specified target. Each range covers every literal
short case in its seeds; none of these definitions asserts coverage.
The range assembly retains the original 122-seed domain and all 15 catalogues.
Source: Parrott (1972), section 5, p.683; the parent source READMEs.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction

/-- Arithmetic coverage on a consecutive range of the original seed indices. -/
def CoverageOn (start count : Nat) : Prop :=
  ∀ i : Fin 122, start ≤ i.val → i.val < start + count → Coverage i (stepData i)

/-- All remaining finite checks, with no membership or order premise. -/
def NumericCoverage : Prop := ∀ i, Coverage i (stepData i)

theorem numericCoverage_of_ranges (h₀ : CoverageOn 0 40) (h₁ : CoverageOn 40 40)
    (h₂ : CoverageOn 80 42) : NumericCoverage := by
  intro i
  by_cases h : i.val < 40
  · exact h₀ i (by omega) h
  · by_cases h' : i.val < 80
    · exact h₁ i (by omega) h'
    · exact h₂ i (by omega) i.isLt

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
