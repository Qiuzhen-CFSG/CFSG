module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FirstProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.Y
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.W
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.Z
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.V
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.W2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.W3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.W6
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.V2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.V4

/-!
# The exact two positive source words from a fixed multiplication circuit

The first product is completely checked in `FirstProduct`. The four remaining
prefix products and the seven power products below are explicit numerical
obligations on fixed tables. They must all be discharged before either source
relation is unconditional. Multiplication is in the literal row convention.
See `source/README.md` for the ATLAS source and every circuit edge.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords
theorem wordThree_eq
    (hy : Data.x.matrix * Data.b.matrix = Data.y.matrix)
    (hw : Data.y.matrix * Data.x.matrix = Data.w.matrix) :
    Data1242.first * Data1242.second^2 * Data1242.first * Data1242.second = Data.w.matrix := by
  rw [← Sources.first_matrix, ← Sources.second_matrix]
  calc
    _ = (Data.a.matrix * Data.b.matrix * Data.b.matrix) *
        (Data.a.matrix * Data.b.matrix) := by simp only [pow_two, mul_assoc]
    _ = Data.w.matrix := by simp only [FirstProduct.matrix_product, hy, hw]

theorem wordFour_eq
    (hy : Data.x.matrix * Data.b.matrix = Data.y.matrix)
    (hw : Data.y.matrix * Data.x.matrix = Data.w.matrix)
    (hz : Data.y.matrix * Data.w.matrix = Data.z.matrix)
    (hv : Data.z.matrix * Data.x.matrix = Data.v.matrix) :
    Data1242.first * Data1242.second^2 * Data1242.first * Data1242.second^2 *
      Data1242.first * Data1242.second * Data1242.first * Data1242.second = Data.v.matrix := by
  have hy' : Data.y.matrix = Data1242.first * Data1242.second^2 := by
    rw [← hy, ← FirstProduct.literal_product, Sources.second_matrix, pow_two, mul_assoc]
  rw [← hv, ← hz, hy', ← wordThree_eq hy hw, ← FirstProduct.literal_product]
  simp only [pow_two, mul_assoc]

theorem twelfth_of_products
    (h2 : Data.w.matrix * Data.w.matrix = Data.w2.matrix)
    (h3 : Data.w2.matrix * Data.w.matrix = Data.w3.matrix)
    (h6 : Data.w3.matrix * Data.w3.matrix = Data.w6.matrix)
    (h12 : Data.w6.matrix * Data.w6.matrix = Data.one.matrix) :
    Data.w.matrix^12 = 1 := by
  have h3' : Data.w.matrix^3 = Data.w3.matrix := by
    simpa only [pow_succ, pow_zero, one_mul, h2] using h3
  calc
    _ = ((Data.w.matrix^3)^2)^2 := by simp only [← pow_mul]
    _ = 1 := by simp only [h3', pow_two, h6, h12, Sources.identity_matrix]

theorem fifth_of_products
    (h2 : Data.v.matrix * Data.v.matrix = Data.v2.matrix)
    (h4 : Data.v2.matrix * Data.v2.matrix = Data.v4.matrix)
    (h5 : Data.v4.matrix * Data.v.matrix = Data.one.matrix) :
    Data.v.matrix^5 = 1 := by
  calc
    _ = (Data.v.matrix^2)^2 * Data.v.matrix := by
      rw [← pow_mul]
      exact pow_succ Data.v.matrix 4
    _ = 1 := by simp only [pow_two, h2, h4, h5, Sources.identity_matrix]

theorem commutator_order12_of_products
    (hy : Data.x.matrix * Data.b.matrix = Data.y.matrix)
    (hw : Data.y.matrix * Data.x.matrix = Data.w.matrix)
    (h2 : Data.w.matrix * Data.w.matrix = Data.w2.matrix)
    (h3 : Data.w2.matrix * Data.w.matrix = Data.w3.matrix)
    (h6 : Data.w3.matrix * Data.w3.matrix = Data.w6.matrix)
    (h12 : Data.w6.matrix * Data.w6.matrix = Data.one.matrix) :
    (Data1242.first * Data1242.second^2 * Data1242.first * Data1242.second)^12 = 1 := by
  rw [wordThree_eq hy hw]
  exact twelfth_of_products h2 h3 h6 h12

theorem second_commutator_order5_of_products
    (hy : Data.x.matrix * Data.b.matrix = Data.y.matrix)
    (hw : Data.y.matrix * Data.x.matrix = Data.w.matrix)
    (hz : Data.y.matrix * Data.w.matrix = Data.z.matrix)
    (hv : Data.z.matrix * Data.x.matrix = Data.v.matrix)
    (h2 : Data.v.matrix * Data.v.matrix = Data.v2.matrix)
    (h4 : Data.v2.matrix * Data.v2.matrix = Data.v4.matrix)
    (h5 : Data.v4.matrix * Data.v.matrix = Data.one.matrix) :
    (Data1242.first * Data1242.second^2 * Data1242.first * Data1242.second^2 *
      Data1242.first * Data1242.second * Data1242.first * Data1242.second)^5 = 1 := by
  rw [wordFour_eq hy hw hz hv]
  exact fifth_of_products h2 h4 h5

theorem third_source_word_of_products
    (hy : Data.x.matrix * Data.b.matrix = Data.y.matrix)
    (hw : Data.y.matrix * Data.x.matrix = Data.w.matrix)
    (h2 : Data.w.matrix * Data.w.matrix = Data.w2.matrix)
    (h3 : Data.w2.matrix * Data.w.matrix = Data.w3.matrix)
    (h6 : Data.w3.matrix * Data.w3.matrix = Data.w6.matrix)
    (h12 : Data.w6.matrix * Data.w6.matrix = Data.one.matrix) :
    Presentation.rowRelatorValues Data1242.first Data1242.second 3 = 1 := by
  simpa [Presentation.rowRelatorValues] using commutator_order12_of_products hy hw h2 h3 h6 h12

theorem fourth_source_word_of_products
    (hy : Data.x.matrix * Data.b.matrix = Data.y.matrix)
    (hw : Data.y.matrix * Data.x.matrix = Data.w.matrix)
    (hz : Data.y.matrix * Data.w.matrix = Data.z.matrix)
    (hv : Data.z.matrix * Data.x.matrix = Data.v.matrix)
    (h2 : Data.v.matrix * Data.v.matrix = Data.v2.matrix)
    (h4 : Data.v2.matrix * Data.v2.matrix = Data.v4.matrix)
    (h5 : Data.v4.matrix * Data.v.matrix = Data.one.matrix) :
    Presentation.rowRelatorValues Data1242.first Data1242.second 4 = 1 := by
  simpa [Presentation.rowRelatorValues] using
    second_commutator_order5_of_products hy hw hz hv h2 h4 h5
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords
