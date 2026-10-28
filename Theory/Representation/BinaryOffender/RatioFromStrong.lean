module

public import Theory.Representation.BinaryOffender.Replacement

/-!
# Determining the quadratic ratio from strong offenders

Without strong offenders an FF-module has quadratic ratio one. If all strong
offenders have the same action ratio, that value is the quadratic ratio:
Thompson replacement supplies a quadratic strong offender attaining it, and
every other elementary subgroup has ratio at least one.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definitions B.1.1–B.1.3 and Thompson replacement B.1.4, printed pp. 67–69.
-/

public section
namespace Representation.BinaryOffender
open scoped ENNReal

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem quadraticRatio_eq_one_of_no_strong (hff : IsFFModule ρ)
    (hstrong : ∀ A, ¬ IsStrongOffender ρ A) : quadraticRatio ρ = 1 := by
  apply le_antisymm ((isFFModule_iff_quadraticRatio_le_one ρ).mp hff)
  apply le_of_not_gt
  intro hlt
  obtain ⟨A, hA⟩ := (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mpr hlt
  exact hstrong A hA

theorem quadraticRatio_eq_of_strong_ratios {r : ℝ≥0∞}
    (hex : IsStrongFFModule ρ)
    (hr : ∀ A, IsStrongOffender ρ A → actionRatio ρ A = r) :
    quadraticRatio ρ = r := by
  obtain ⟨A, hA⟩ := hex
  have hr1 : r < 1 := by
    rw [← hr A hA]
    exact (actionRatio_lt_one_iff ρ hA.1).mpr hA.2
  apply le_antisymm
  · obtain ⟨B, _, hB, hquad, hstrong⟩ := hA.exists_quadratic_minimalBestOffender ρ
    rw [← hr B hstrong]
    exact iInf_le_of_le B (iInf_le_of_le ⟨hB.1.1, hquad⟩ le_rfl)
  · refine le_iInf fun B => le_iInf fun hB => ?_
    by_cases hs : IsStrongOffender ρ B
    · exact (hr B hs).ge
    · apply hr1.le.trans
      apply le_of_not_gt
      intro hlt
      exact hs ⟨hB.1, (actionRatio_lt_one_iff ρ hB.1).mp hlt⟩

end Representation.BinaryOffender
