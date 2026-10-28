module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeLower
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeUpper
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.FourPowers

/-!
# Assembly of the two fixed commutator-table power chains

Four checked literal products give the twelfth power, and three give the fifth.
Every intermediate table is fixed in `TablePowers.Data`; its name supplies no
power identity. The complete original-table comparisons and identity comparison
connect the product certificates to the two unconditional power equations.

These equations concern the candidate tables themselves. Their comparison to
the original positive words remains with `CommutatorWords`' separate comparison
owner. Source: ATLAS M24G1-P1; see `TablePowers/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords
open TablePowers.Data

/-- Assemble the literal twelfth-power chain once all four products are checked. -/
theorem wordThree_pow_twelve_of_products
    (h₂ : three * three = threeSquare)
    (h₃ : threeSquare * three = threeCube)
    (h₆ : threeCube * threeCube = threeSixth)
    (h₁₂ : threeSixth * threeSixth = identity) : Data.wordThree ^ 12 = 1 := by
  have hc : three ^ 3 = threeCube := by
    calc
      three ^ 3 = three ^ 2 * three := pow_succ _ 2
      _ = threeSquare * three := by rw [pow_two, h₂]
      _ = threeCube := h₃
  have hs : three ^ 6 = threeSixth := by
    calc
      three ^ 6 = (three ^ 3) ^ 2 := (pow_mul _ 3 2)
      _ = threeSixth := by rw [hc, pow_two, h₆]
  rw [← three_original]
  calc
    three ^ 12 = (three ^ 6) ^ 2 := (pow_mul _ 6 2)
    _ = identity := by rw [hs, pow_two, h₁₂]
    _ = 1 := identity_eq_one

/-- Assemble the literal fifth-power chain once all three products are checked. -/
theorem wordFour_pow_five_of_products
    (h₂ : four * four = fourSquare)
    (h₄ : fourSquare * fourSquare = fourFourth)
    (h₅ : fourFourth * four = identity) : Data.wordFour ^ 5 = 1 := by
  have hq : four ^ 4 = fourFourth := by
    calc
      four ^ 4 = (four ^ 2) ^ 2 := (pow_mul _ 2 2)
      _ = fourFourth := by simp only [pow_two, h₂, h₄]
  rw [← four_original]
  calc
    four ^ 5 = four ^ 4 * four := pow_succ _ 4
    _ = identity := by rw [hq, h₅]
    _ = 1 := identity_eq_one

/-- The fixed degree-1792 three-word candidate has twelfth power equal to one. -/
theorem wordThree_pow_twelve : Data.wordThree ^ 12 = 1 :=
  wordThree_pow_twelve_of_products
    TablePowers.ThreeLower.square TablePowers.ThreeLower.cube
    TablePowers.ThreeUpper.sixth TablePowers.ThreeUpper.closing

/-- The fixed degree-1792 four-word candidate has fifth power equal to one. -/
theorem wordFour_pow_five : Data.wordFour ^ 5 = 1 :=
  wordFour_pow_five_of_products
    TablePowers.FourPowers.square TablePowers.FourPowers.fourth
    TablePowers.FourPowers.closing

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords
