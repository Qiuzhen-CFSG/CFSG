module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.Circuit
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts

/-!
# The last two positive ATLAS words in degree 1242

The checked first product and shared prefixes identify the literal words with
the fixed intermediate matrices. Complete cube and fourth-power certificates
then discharge every premise of the circuit, proving both relators on the
original untransposed generators without further hypotheses.

These are exactly indices 5 and 6 of `Presentation.rowRelatorValues`.
Source: John Bray's ATLAS M24G1-P1 and M24G1-f2r1242B0.m1/.m2;
see `MixedWords/source/README.md` for the circuit and certificate details.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242

/-- The product of cubes in ATLAS positive row word 5. -/
theorem mixed_cube_product :
    (Data1242.first * Data1242.second * Data1242.first * Data1242.second *
        Data1242.first * Data1242.second ^ 2) ^ 3 *
      (Data1242.first * Data1242.second * Data1242.first * Data1242.second ^ 2 *
        Data1242.first * Data1242.second ^ 2) ^ 3 = 1 :=
  MixedWords.fifth_word_of_prefix_products MixedWords.y_product MixedWords.z_product
    MixedWords.u_product MixedWords.v_product

/-- The nested fourth power in ATLAS positive row word 6. -/
theorem last_word_order4 :
    (Data1242.first * Data1242.second *
      (Data1242.first * Data1242.second * Data1242.first * Data1242.second ^ 2) ^ 3) ^ 4 = 1 :=
  MixedWords.sixth_word_of_prefix_products MixedWords.y_product MixedWords.z_product

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
