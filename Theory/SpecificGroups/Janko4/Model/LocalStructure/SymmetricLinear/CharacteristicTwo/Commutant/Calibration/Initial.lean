module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Checker

/-!
# Checked initial for the max4 commutant

The four initial orbit rows and their expressions are the literal coordinate rows.
These certificates discharge `InitialCheck` in `lowerTriangular_of_checks`.
Source: `../source/README.md` and `../../source/reconstruction.json`.
Regenerate these proof declarations with `Calibration/source/generate.py`.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof

-- Avoid checking several substantial fixed-table reductions concurrently.
set_option Elab.async false

private theorem initial_0 : InitialCheck 0 := by
  unfold InitialCheck
  decide +kernel

private theorem initial_1 : InitialCheck 1 := by
  unfold InitialCheck
  decide +kernel

private theorem initial_2 : InitialCheck 2 := by
  unfold InitialCheck
  decide +kernel

private theorem initial_3 : InitialCheck 3 := by
  unfold InitialCheck
  decide +kernel

attribute [local irreducible] InitialCheck

theorem initial_checked : ∀ i, InitialCheck i := by
  intro i
  fin_cases i
  · exact initial_0
  · exact initial_1
  · exact initial_2
  · exact initial_3

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof
