module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Products
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Circuit

/-!
# The fifth power of the fixed degree-1242 second commutator

The three certified products `v*v=v2`, `v2*v2=v4` and `v4*v=one` give
`v^5=1`; the existing source bridge identifies `one` with the matrix identity.
The application to the original positive word retains exactly the four prefix
products, whose independent producer is owned by the commutator assembly.
Source: John Bray, ATLAS M24G1-P1, literal untransposed M24G1-f2r1242B0
matrices. See `FifthPower/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower
theorem fifth_power : Data.v.matrix ^ 5 = 1 :=
  fifth_of_products Products.square Products.fourth Products.final_product

/-- The original positive source word, conditional only on its four prefixes. -/
theorem second_commutator_order5_of_prefix
    (hy : Data.x.matrix * Data.b.matrix = Data.y.matrix)
    (hw : Data.y.matrix * Data.x.matrix = Data.w.matrix)
    (hz : Data.y.matrix * Data.w.matrix = Data.z.matrix)
    (hv : Data.z.matrix * Data.x.matrix = Data.v.matrix) :
    (Data1242.first * Data1242.second^2 * Data1242.first * Data1242.second^2 *
      Data1242.first * Data1242.second * Data1242.first * Data1242.second)^5 = 1 := by
  rw [wordFour_eq hy hw hz hv]
  exact fifth_power

/-- The row relator at source index 4 (zero-based). -/
theorem fourth_source_word_of_prefix
    (hy : Data.x.matrix * Data.b.matrix = Data.y.matrix)
    (hw : Data.y.matrix * Data.x.matrix = Data.w.matrix)
    (hz : Data.y.matrix * Data.w.matrix = Data.z.matrix)
    (hv : Data.z.matrix * Data.x.matrix = Data.v.matrix) :
    Presentation.rowRelatorValues Data1242.first Data1242.second 4 = 1 := by
  simpa [Presentation.rowRelatorValues] using
    second_commutator_order5_of_prefix hy hw hz hv
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower
