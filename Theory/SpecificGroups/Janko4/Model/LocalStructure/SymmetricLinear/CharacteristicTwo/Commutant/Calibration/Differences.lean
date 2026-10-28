module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Checker

/-!
# Checked differences for the max4 commutant

Every row of qₐ−I agrees with the original `conjugateRows`.
These certificates discharge `DifferenceCheck` in `lowerTriangular_of_checks`.
Source: `../source/README.md` and `../../source/reconstruction.json`.
Regenerate these proof declarations with `Calibration/source/generate.py`.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof

-- Avoid checking several substantial fixed-table reductions concurrently.
set_option Elab.async false

private theorem difference_0 : DifferenceCheck 0 := by
  unfold DifferenceCheck
  decide +kernel

private theorem difference_1 : DifferenceCheck 1 := by
  unfold DifferenceCheck
  decide +kernel

private theorem difference_2 : DifferenceCheck 2 := by
  unfold DifferenceCheck
  decide +kernel

private theorem difference_3 : DifferenceCheck 3 := by
  unfold DifferenceCheck
  decide +kernel

private theorem difference_4 : DifferenceCheck 4 := by
  unfold DifferenceCheck
  decide +kernel

private theorem difference_5 : DifferenceCheck 5 := by
  unfold DifferenceCheck
  decide +kernel

private theorem difference_6 : DifferenceCheck 6 := by
  unfold DifferenceCheck
  decide +kernel

private theorem difference_7 : DifferenceCheck 7 := by
  unfold DifferenceCheck
  decide +kernel

private theorem difference_8 : DifferenceCheck 8 := by
  unfold DifferenceCheck
  decide +kernel

private theorem difference_9 : DifferenceCheck 9 := by
  unfold DifferenceCheck
  decide +kernel

private theorem difference_10 : DifferenceCheck 10 := by
  unfold DifferenceCheck
  decide +kernel

attribute [local irreducible] DifferenceCheck

theorem differences_checked : ∀ i, DifferenceCheck i := by
  intro i
  fin_cases i
  · exact difference_0
  · exact difference_1
  · exact difference_2
  · exact difference_3
  · exact difference_4
  · exact difference_5
  · exact difference_6
  · exact difference_7
  · exact difference_8
  · exact difference_9
  · exact difference_10

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof
