module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.ResidualFixer
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Coverage

/-!
# Pointwise fixation of the actual projective graph-field residual

The diagonal and cycle subgroup lies in the embedded two-residual of the
fixed subgroup of inverse transpose times Frobenius on PSL₃(4). Hence every
automorphism fixing that residual pointwise fixes the matrix subgroup.
The proved full automorphism coverage and matrix fixer calculation place it
in the image of the order-eighteen group `model × C₂`. Its order therefore
divides eighteen and is not divisible by four.

Source: Aschbacher--Smith 15.3.38, printed p.1137, combined manuscript of
1 March 2004 (`refs/quasithin.pdf`). This supplies the projective divisibility
bound for the central-cover argument without using the printed assertion
that the entire automorphism centralizer has order two. Only containment of
the concrete matrix subgroup in the actual residual is needed.
-/

public section

open Subgroup
namespace Matrix.PSL3Four
open ExtendedCentralizer.ProjectiveFixer

/-- The full pointwise fixer of the embedded graph-field two-residual has
order dividing eighteen, with no automorphism-coverage premise. -/
theorem projectiveGraphFieldResidual_fixer_card_dvd :
    Nat.card (fixingSubgroup (MulAut PSL) (projectiveGraphFieldResidual : Set PSL)) ∣ 18 := by
  have hle : fixingSubgroup (MulAut PSL) (projectiveGraphFieldResidual : Set PSL) ≤
      fixer model := by
    rw [fixer, InnerFamilyNormalizer.QuaternionPlacement.standard_eq_top, top_inf_eq]
    exact fixingSubgroup_antitone (MulAut PSL) PSL
      InnerFamilyNormalizer.model_le_projectiveResidual
  exact (card_dvd_of_le hle).trans (by
    rw [model_fixer_eq_candidate]
    exact candidate_card_dvd)

/-- Four does not divide the order of the pointwise automorphism fixer of
the actual projective graph-field residual. -/
theorem projectiveGraphFieldResidual_fixer_not_four :
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut PSL)
      (projectiveGraphFieldResidual : Set PSL)) := by
  intro hfour
  exact (by decide : ¬ 4 ∣ 18) (hfour.trans projectiveGraphFieldResidual_fixer_card_dvd)

end Matrix.PSL3Four
