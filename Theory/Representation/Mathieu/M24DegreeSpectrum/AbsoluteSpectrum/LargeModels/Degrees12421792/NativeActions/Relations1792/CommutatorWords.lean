module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.MonomialRows
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers

/-!
# Certificates for the two degree-1792 positive commutator words

The complete table comparisons identify both positive source words with fixed
binary matrices. Their checked power chains give the twelfth- and fifth-power
equations below, with every numerical premise discharged. These equations use
the original untransposed matrices and supply indices 3 and 4 of
`Presentation.rowRelatorValues` without assuming any generator-order equation.

Source: John Bray, ATLAS M24G1-P1 and M24G1-f2r1792B0.m1/.m2.
The row convention and inverse-elimination interpretation are in `Presentation`.
See `CommutatorWords/source/README.md` for provenance and checked scope.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792

/-- The first positive commutator word satisfies the source twelfth-power equation. -/
theorem commutator_order12 :
    (Data1792.first * Data1792.second ^ 2 * Data1792.first * Data1792.second) ^ 12 = 1 := by
  rw [CommutatorWords.wordThree_eq]
  exact CommutatorWords.wordThree_pow_twelve

/-- The second positive commutator word satisfies the source fifth-power equation. -/
theorem second_commutator_order5 :
    (Data1792.first * Data1792.second ^ 2 * Data1792.first * Data1792.second ^ 2 *
      Data1792.first * Data1792.second * Data1792.first * Data1792.second) ^ 5 = 1 := by
  rw [CommutatorWords.wordFour_eq]
  exact CommutatorWords.wordFour_pow_five

namespace CommutatorWords

/-- The unconditional row relation at source index 3 (zero-based). -/
theorem third_source_word :
    Presentation.rowRelatorValues Data1792.first Data1792.second 3 = 1 := by
  simpa [Presentation.rowRelatorValues] using commutator_order12

/-- The unconditional row relation at source index 4 (zero-based). -/
theorem fourth_source_word :
    Presentation.rowRelatorValues Data1792.first Data1792.second 4 = 1 := by
  simpa [Presentation.rowRelatorValues] using second_commutator_order5

end CommutatorWords
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
