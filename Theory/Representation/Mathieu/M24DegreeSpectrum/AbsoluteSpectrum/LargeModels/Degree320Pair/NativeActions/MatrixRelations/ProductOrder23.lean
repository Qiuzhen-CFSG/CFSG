module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C1a
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C2a
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C3a
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C5a
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C10a
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C20a
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C23a
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C1b
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C2b
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C3b
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C5b
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C10b
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C20b
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.ProductOrder23.C23b

/-!
# The literal degree-320 ATLAS product has order dividing 23

For each original matrix pair, checked packed products establish the exponent
chain 1, 2, 3, 5, 10, 20, 23. The last decoded matrix is the identity.
Associativity and the power laws then prove the third relation of John Bray's
M24G1-P1, without any generator-order or presentation-exactness premise.
False denotes 320a and true denotes 320b; neither matrix is transposed.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/M24G1-P1.
See `ProductOrder23/source/README.md` for provenance and kernel-check timings.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate

private theorem power23_of_chain {M : Type*} [Monoid M]
    (x p2 p3 p5 p10 p20 : M)
    (h2 : x * x = p2) (h3 : p2 * x = p3) (h5 : p3 * p2 = p5)
    (h10 : p5 * p5 = p10) (h20 : p10 * p10 = p20) (h23 : p20 * p3 = 1) :
    x ^ 23 = 1 := by
  have hp2 : x ^ 2 = p2 := by simpa only [pow_two] using h2
  have hp3 : x ^ 3 = p3 := calc
    x ^ 3 = x ^ 2 * x := pow_succ x 2
    _ = p3 := by rw [hp2, h3]
  have hp5 : x ^ 5 = p5 := calc
    x ^ 5 = x ^ 3 * x ^ 2 := pow_add x 3 2
    _ = p5 := by rw [hp3, hp2, h5]
  have hp10 : x ^ 10 = p10 := calc
    x ^ 10 = x ^ 5 * x ^ 5 := pow_add x 5 5
    _ = p10 := by rw [hp5, h10]
  have hp20 : x ^ 20 = p20 := calc
    x ^ 20 = x ^ 10 * x ^ 10 := pow_add x 10 10
    _ = p20 := by rw [hp10, h20]
  calc
    x ^ 23 = x ^ 20 * x ^ 3 := pow_add x 20 3
    _ = 1 := by rw [hp20, hp3, h23]

/-- The order-23 relation on the two literal, untransposed ATLAS pairs.
This supplies exactly `h23` of `matrixRelations_of_remaining`. -/
theorem product_order23 (variant : Bool) :
    (matrixA variant * matrixB variant) ^ 23 = 1 := by
  cases variant
  · change (Thompson.BinaryMatrix.decode 320 Data.AaRows.toArray *
      Thompson.BinaryMatrix.decode 320 Data.BaRows.toArray) ^ 23 = 1
    rw [Order23.C1a.product]
    exact power23_of_chain _ _ _ _ _ _ Order23.C2a.product Order23.C3a.product
      Order23.C5a.product Order23.C10a.product Order23.C20a.product
      (Order23.C23a.product.trans decode_identityRows)
  · change (Thompson.BinaryMatrix.decode 320 Data.AbRows.toArray *
      Thompson.BinaryMatrix.decode 320 Data.BbRows.toArray) ^ 23 = 1
    rw [Order23.C1b.product]
    exact power23_of_chain _ _ _ _ _ _ Order23.C2b.product Order23.C3b.product
      Order23.C5b.product Order23.C10b.product Order23.C20b.product
      (Order23.C23b.product.trans decode_identityRows)

/-- Literal zero-indexed clause 2 of the shared positive source presentation. -/
theorem product_order23_source_clause (variant : Bool) :
    Degrees12421792.NativeActions.Presentation.rowRelatorValues
      (matrixA variant) (matrixB variant) (2 : Fin 7) = 1 :=
  product_order23 variant

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
