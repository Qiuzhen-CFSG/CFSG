module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixProducts.Y
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixProducts.Z
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixProducts.U
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixProducts.V
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.Circuit

/-!+# Four shared prefixes of the last two ATLAS words in degree 1242

The fixed untransposed matrices satisfy XB = Y, XY = Z, XZ = U and ZY = V.
Each product follows from complete, kernel-checked row certificates. Together
with the already proved AB = X, they discharge every shared prefix in source
clauses 5 and 6. The five cube products and five fourth-power products remain
explicit in the two applications below, for their independent producers.

Source: John Bray's ATLAS M24G1-P1 and M24G1-f2r1242B0.m1/.m2;
see `PrefixProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords

/-- Source clause 5 with all shared prefix products discharged. The remaining
five numerical products belong to the independent cube-product certificate. -/
theorem fifth_word_of_cube_products
    (hu2 : Data.u * Data.u = Data.u2)
    (hu3 : Data.u2 * Data.u = Data.u3)
    (hv2 : Data.v * Data.v = Data.v2)
    (hv3 : Data.v2 * Data.v = Data.v3)
    (hinv : Data.u3 * Data.v3 = 1) :
    Presentation.rowRelatorValues Data1242.first Data1242.second 5 = 1 :=
  fifth_word_of_products y_product z_product u_product v_product hu2 hu3 hv2 hv3 hinv

/-- Source clause 6 with both shared prefix products discharged. The remaining
five numerical products belong to the independent fourth-power certificate. -/
theorem sixth_word_of_fourth_products
    (hz2 : Data.z * Data.z = Data.z2)
    (hz3 : Data.z2 * Data.z = Data.z3)
    (ht : Data.x * Data.z3 = Data.t)
    (ht2 : Data.t * Data.t = Data.t2)
    (hsq : Data.t2 * Data.t2 = 1) :
    Presentation.rowRelatorValues Data1242.first Data1242.second 6 = 1 :=
  sixth_word_of_products y_product z_product hz2 hz3 ht ht2 hsq

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
