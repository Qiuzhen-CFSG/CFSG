module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.X
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.Y
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.W
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.U
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.V
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.U2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.U3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.V2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.V3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.Cubes
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.W2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.W3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.T
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.T2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.A.Last
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.X
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.Y
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.W
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.U
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.V
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.U2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.U3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.V2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.V3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.Cubes
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.W2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.W3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.T
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.T2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.MixedRelators.B.Last

/-!
# The two mixed ATLAS relations for both binary degree-320 matrix pairs

Fifteen explicit products per variant certify the two mixed words. The
sparse-row checker reconstructs the literal masks and computes each product
by XOR. Monoid associativity identifies the shared intermediate words with
clauses 5 and 6 of `Presentation.rowRelatorValues`.

All matrices are the original untransposed ATLAS rows; false selects 320a
and true selects 320b. No native action, presentation comparison, generator
order, density, trace, or other relation certificate is assumed.

Source: John Bray, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/M24G1-P1.
Numerical provenance and measurements: `MixedRelators/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
open Thompson.BinaryMatrix

private theorem mixedWordAssembly {M : Type*} [Monoid M] (a b x y w u v u2 u3 v2 v3 w2 w3 t t2 : M)
    (hx : a * b = x) (hy : x * b = y) (hw : x * y = w)
    (hu : x * w = u) (hv : w * y = v)
    (hu2 : u * u = u2) (hu3 : u * u2 = u3)
    (hv2 : v * v = v2) (hv3 : v * v2 = v3)
    (hc : u3 * v3 = 1) (hw2 : w * w = w2) (hw3 : w * w2 = w3)
    (ht : x * w3 = t) (ht2 : t * t = t2) (h4 : t2 * t2 = 1) :
    (a * b * a * b * a * b ^ 2) ^ 3 * (a * b * a * b ^ 2 * a * b ^ 2) ^ 3 = 1 ∧
    (a * b * (a * b * a * b ^ 2) ^ 3) ^ 4 = 1 := by
  subst x y w u v u2 u3 v2 v3 w2 w3 t t2
  constructor
  · simpa only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using hc
  · simpa only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h4

private theorem relations_false :
    (matrixA false * matrixB false * matrixA false * matrixB false * matrixA false * matrixB false ^ 2) ^ 3 *
      (matrixA false * matrixB false * matrixA false * matrixB false ^ 2 * matrixA false * matrixB false ^ 2) ^ 3 = 1 ∧
    (matrixA false * matrixB false * (matrixA false * matrixB false * matrixA false * matrixB false ^ 2) ^ 3) ^ 4 = 1 :=
  mixedWordAssembly (matrixA false) (matrixB false)
    (decode 320 MixedRelators.A.X.rows.toArray)
    (decode 320 MixedRelators.A.Y.rows.toArray)
    (decode 320 MixedRelators.A.W.rows.toArray)
    (decode 320 MixedRelators.A.U.rows.toArray)
    (decode 320 MixedRelators.A.V.rows.toArray)
    (decode 320 MixedRelators.A.U2.rows.toArray)
    (decode 320 MixedRelators.A.U3.rows.toArray)
    (decode 320 MixedRelators.A.V2.rows.toArray)
    (decode 320 MixedRelators.A.V3.rows.toArray)
    (decode 320 MixedRelators.A.W2.rows.toArray)
    (decode 320 MixedRelators.A.W3.rows.toArray)
    (decode 320 MixedRelators.A.T.rows.toArray)
    (decode 320 MixedRelators.A.T2.rows.toArray)
    MixedRelators.A.X_product
    MixedRelators.A.Y_product
    MixedRelators.A.W_product
    MixedRelators.A.U_product
    MixedRelators.A.V_product
    MixedRelators.A.U2_product
    MixedRelators.A.U3_product
    MixedRelators.A.V2_product
    MixedRelators.A.V3_product
    MixedRelators.A.Cubes_product
    MixedRelators.A.W2_product
    MixedRelators.A.W3_product
    MixedRelators.A.T_product
    MixedRelators.A.T2_product
    MixedRelators.A.Last_product

private theorem relations_true :
    (matrixA true * matrixB true * matrixA true * matrixB true * matrixA true * matrixB true ^ 2) ^ 3 *
      (matrixA true * matrixB true * matrixA true * matrixB true ^ 2 * matrixA true * matrixB true ^ 2) ^ 3 = 1 ∧
    (matrixA true * matrixB true * (matrixA true * matrixB true * matrixA true * matrixB true ^ 2) ^ 3) ^ 4 = 1 :=
  mixedWordAssembly (matrixA true) (matrixB true)
    (decode 320 MixedRelators.B.X.rows.toArray)
    (decode 320 MixedRelators.B.Y.rows.toArray)
    (decode 320 MixedRelators.B.W.rows.toArray)
    (decode 320 MixedRelators.B.U.rows.toArray)
    (decode 320 MixedRelators.B.V.rows.toArray)
    (decode 320 MixedRelators.B.U2.rows.toArray)
    (decode 320 MixedRelators.B.U3.rows.toArray)
    (decode 320 MixedRelators.B.V2.rows.toArray)
    (decode 320 MixedRelators.B.V3.rows.toArray)
    (decode 320 MixedRelators.B.W2.rows.toArray)
    (decode 320 MixedRelators.B.W3.rows.toArray)
    (decode 320 MixedRelators.B.T.rows.toArray)
    (decode 320 MixedRelators.B.T2.rows.toArray)
    MixedRelators.B.X_product
    MixedRelators.B.Y_product
    MixedRelators.B.W_product
    MixedRelators.B.U_product
    MixedRelators.B.V_product
    MixedRelators.B.U2_product
    MixedRelators.B.U3_product
    MixedRelators.B.V2_product
    MixedRelators.B.V3_product
    MixedRelators.B.Cubes_product
    MixedRelators.B.W2_product
    MixedRelators.B.W3_product
    MixedRelators.B.T_product
    MixedRelators.B.T2_product
    MixedRelators.B.Last_product

/-- The product of cubes in the sixth positive ATLAS relator. -/
theorem mixed_cubes (variant : Bool) :
    (matrixA variant * matrixB variant * matrixA variant * matrixB variant *
      matrixA variant * matrixB variant ^ 2) ^ 3 *
    (matrixA variant * matrixB variant * matrixA variant * matrixB variant ^ 2 *
      matrixA variant * matrixB variant ^ 2) ^ 3 = 1 := by
  cases variant
  · exact relations_false.1
  · exact relations_true.1

/-- The order-four word in the seventh positive ATLAS relator. -/
theorem last_order4 (variant : Bool) :
    (matrixA variant * matrixB variant *
      (matrixA variant * matrixB variant * matrixA variant * matrixB variant ^ 2) ^ 3) ^ 4 = 1 := by
  cases variant
  · exact relations_false.2
  · exact relations_true.2

/-- Application to zero-based source clause 5 on the literal matrices. -/
theorem rowRelatorValues_five (variant : Bool) :
    Degrees12421792.NativeActions.Presentation.rowRelatorValues
      (matrixA variant) (matrixB variant) 5 = 1 :=
  mixed_cubes variant

/-- Application to zero-based source clause 6 on the literal matrices. -/
theorem rowRelatorValues_six (variant : Bool) :
    Degrees12421792.NativeActions.Presentation.rowRelatorValues
      (matrixA variant) (matrixB variant) 6 = 1 :=
  last_order4 variant

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
