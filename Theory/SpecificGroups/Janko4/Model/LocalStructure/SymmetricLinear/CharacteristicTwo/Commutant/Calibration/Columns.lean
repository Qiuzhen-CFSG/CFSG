module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Checker

/-!
# Checked columns for the max4 commutant

Every bit of the eleven column tables is the corresponding difference-row bit.
These certificates discharge `ColumnCheck` in `lowerTriangular_of_checks`.
Source: `../source/README.md` and `../../source/reconstruction.json`.
Regenerate these proof declarations with `Calibration/source/generate.py`.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof

-- Avoid checking several substantial fixed-table reductions concurrently.
set_option Elab.async false

private theorem column_0 : ColumnCheck 0 :=
  Calibration.column_of_div 0 (by decide +kernel)

private theorem column_1 : ColumnCheck 1 :=
  Calibration.column_of_div 1 (by decide +kernel)

private theorem column_2 : ColumnCheck 2 :=
  Calibration.column_of_div 2 (by decide +kernel)

private theorem column_3 : ColumnCheck 3 :=
  Calibration.column_of_div 3 (by decide +kernel)

private theorem column_4 : ColumnCheck 4 :=
  Calibration.column_of_div 4 (by decide +kernel)

private theorem column_5 : ColumnCheck 5 :=
  Calibration.column_of_div 5 (by decide +kernel)

private theorem column_6 : ColumnCheck 6 :=
  Calibration.column_of_div 6 (by decide +kernel)

private theorem column_7 : ColumnCheck 7 :=
  Calibration.column_of_div 7 (by decide +kernel)

private theorem column_8 : ColumnCheck 8 :=
  Calibration.column_of_div 8 (by decide +kernel)

private theorem column_9 : ColumnCheck 9 :=
  Calibration.column_of_div 9 (by decide +kernel)

private theorem column_10 : ColumnCheck 10 :=
  Calibration.column_of_div 10 (by decide +kernel)

attribute [local irreducible] ColumnCheck

theorem columns_checked : ∀ i, ColumnCheck i := by
  intro i
  fin_cases i
  · exact column_0
  · exact column_1
  · exact column_2
  · exact column_3
  · exact column_4
  · exact column_5
  · exact column_6
  · exact column_7
  · exact column_8
  · exact column_9
  · exact column_10

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof
