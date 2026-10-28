module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1242
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Circuit
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.TwelfthPower
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower

/-!
# Degree-1242 commutator word certificates

The checked prefixes identify the two positive source words with the fixed
matrices `w` and `v`. Their checked power products give the twelfth- and
fifth-power equations below, with every numerical premise discharged.
Both equations use the literal untransposed ATLAS matrices, and supply
indices 3 and 4 of `Presentation.rowRelatorValues` for the seven-word assembly.

Source: John Bray, ATLAS M24G1-P1 and M24G1-f2r1242B0.m1/.m2.
See `CommutatorWords/source/README.md` for the circuit, source bridges,
attribution and measured certificate checks.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242

/-- The first positive commutator word satisfies the source twelfth-power equation. -/
theorem commutator_order12 :
    (Data1242.first * Data1242.second^2 * Data1242.first * Data1242.second)^12 = 1 := by
  rw [CommutatorWords.PrefixProducts.wordThree]
  exact CommutatorWords.TwelfthPower.twelfth_power

/-- The second positive commutator word satisfies the source fifth-power equation. -/
theorem second_commutator_order5 :
    (Data1242.first * Data1242.second^2 * Data1242.first * Data1242.second^2 *
      Data1242.first * Data1242.second * Data1242.first * Data1242.second)^5 = 1 := by
  rw [CommutatorWords.PrefixProducts.wordFour]
  exact CommutatorWords.FifthPower.fifth_power

namespace CommutatorWords

/-- The unconditional row relation at source index 3 (zero-based). -/
theorem third_source_word :
    Presentation.rowRelatorValues Data1242.first Data1242.second 3 = 1 := by
  simpa [Presentation.rowRelatorValues] using commutator_order12

/-- The unconditional row relation at source index 4 (zero-based). -/
theorem fourth_source_word :
    Presentation.rowRelatorValues Data1242.first Data1242.second 4 = 1 := by
  simpa [Presentation.rowRelatorValues] using second_commutator_order5

end CommutatorWords
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
