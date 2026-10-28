module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.MonomialArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792

/-!
# Checked monomial rows of the two positive commutator words

We check the partial maps against both original ATLAS arrays, follow the
literal positive words, and compare the resulting rows with the proposed
word tables. Thus every row selected by `wordThreeMap` or `wordFourMap` is
proved, including its comparison to the original matrices. The two final
lemmas leave only the unspecified rows to the dense-certificate producer.

These results do not assert either order equation. Source: ATLAS M24G1-P1,
positive words 3 and 4 in the original row convention; see `source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords
open MonomialArithmetic

set_option maxRecDepth 8192 in
private theorem first_map_checked : checkMap Data1792.firstRows.toList Data.firstMap = true := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_map_checked : checkMap Data1792.secondRows.toList Data.secondMap = true := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem third_map_checked : checkMap Data.wordThreeRows.toList Data.wordThreeMap = true := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem fourth_map_checked : checkMap Data.wordFourRows.toList Data.wordFourMap = true := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem third_paths_checked : checkPaths 1792 Data.firstMap Data.secondMap
    [false, true, true, false, true] Data.wordThreeMap = true := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem fourth_paths_checked : checkPaths 1792 Data.firstMap Data.secondMap
    [false, true, true, false, true, true, false, true, false, true] Data.wordFourMap = true := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_size : Data1792.firstRows.size = 1792 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem second_size : Data1792.secondRows.size = 1792 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem third_size : Data.wordThreeRows.size = 1792 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem fourth_size : Data.wordFourRows.size = 1792 := by decide +kernel

/-- Every row selected by the checked monomial path map agrees with source word 3. -/
theorem wordThree_row_of_monomial (i : Fin 1792)
    (hi : destination Data.wordThreeMap i.val ≠ 0) :
    (Data1792.first * Data1792.second ^ 2 * Data1792.first * Data1792.second) i =
      Data.wordThree i := by
  have hp := rowWord_eq_of_maps Data1792.firstRows Data1792.secondRows Data.wordThreeRows
    Data.firstMap Data.secondMap Data.wordThreeMap [false, true, true, false, true]
    first_map_checked second_map_checked third_map_checked first_size second_size third_size
    third_paths_checked i hi
  change rowWord Data1792.first Data1792.second [false, true, true, false, true] i =
    Data.wordThree i at hp
  simpa only [rowWord, Bool.false_eq_true, ↓reduceIte, mul_one, pow_two, mul_assoc] using hp

/-- Every row selected by the checked monomial path map agrees with source word 4. -/
theorem wordFour_row_of_monomial (i : Fin 1792)
    (hi : destination Data.wordFourMap i.val ≠ 0) :
    (Data1792.first * Data1792.second ^ 2 * Data1792.first * Data1792.second ^ 2 *
      Data1792.first * Data1792.second * Data1792.first * Data1792.second) i =
      Data.wordFour i := by
  have hp := rowWord_eq_of_maps Data1792.firstRows Data1792.secondRows Data.wordFourRows
    Data.firstMap Data.secondMap Data.wordFourMap
    [false, true, true, false, true, true, false, true, false, true]
    first_map_checked second_map_checked fourth_map_checked first_size second_size fourth_size
    fourth_paths_checked i hi
  change rowWord Data1792.first Data1792.second
    [false, true, true, false, true, true, false, true, false, true] i = Data.wordFour i at hp
  simpa only [rowWord, Bool.false_eq_true, ↓reduceIte, mul_one, pow_two, mul_assoc] using hp

/-- Only the unspecified rows remain in the comparison with the first candidate table. -/
theorem wordThree_eq_of_remaining
    (h : ∀ i : Fin 1792, destination Data.wordThreeMap i.val = 0 →
      (Data1792.first * Data1792.second ^ 2 * Data1792.first * Data1792.second) i =
        Data.wordThree i) :
    Data1792.first * Data1792.second ^ 2 * Data1792.first * Data1792.second =
      Data.wordThree := by
  funext i
  by_cases hi : destination Data.wordThreeMap i.val = 0
  · exact h i hi
  · exact wordThree_row_of_monomial i hi

/-- Only the unspecified rows remain in the comparison with the second candidate table. -/
theorem wordFour_eq_of_remaining
    (h : ∀ i : Fin 1792, destination Data.wordFourMap i.val = 0 →
      (Data1792.first * Data1792.second ^ 2 * Data1792.first * Data1792.second ^ 2 *
        Data1792.first * Data1792.second * Data1792.first * Data1792.second) i =
          Data.wordFour i) :
    Data1792.first * Data1792.second ^ 2 * Data1792.first * Data1792.second ^ 2 *
      Data1792.first * Data1792.second * Data1792.first * Data1792.second =
        Data.wordFour := by
  funext i
  by_cases hi : destination Data.wordFourMap i.val = 0
  · exact h i hi
  · exact wordFour_row_of_monomial i hi

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords
