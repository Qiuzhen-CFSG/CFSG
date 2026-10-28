module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.AmbientRows
/-!
# From exact packed products to the actual degree-1000 descent

The ambient packing theorems and literal lift alignment turn each binary tree
product into precisely the corresponding row of `U * ambientA = targetA * U`
or `U * ambientB = targetB * U`. The separate `Consumer` module applies the
complete-family implications to the original descent consumer.

The two numerical families remain explicit until their certificates are proved.
The independent pivot identity occurs only in the separate marked-action consumer.
No rank, representation, simplicity or order assumption enters a matrix identity.

Source: ATLAS HSG1-f2r56B0/HSG1-f2r1000B0 and the literal section1000 candidate;
see `Binary/source/README.md` and `Intertwining/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining
open RowArithmetic

theorem RowTree.vector_product (t : RowTree) (n p : ℕ) (ht : t.Valid)
    (hlen : t.rows.length = n) (x : ℕ) :
    Matrix.vecMul (vector n x) (matrix n p t.rows) = vector p (t.product x) := by
  rw [t.product_eq ht]
  exact (vector_combine t.rows n p hlen x).symm

theorem RowTree.array_mul_row (t : RowTree) (m n p : ℕ) (ht : t.Valid)
    (hlen : t.rows.length = n) (a : Array ℕ) (i : Fin m) :
    (matrix m n a.toList * matrix n p t.rows) i = vector p (t.product a[i.val]!) := by
  funext j
  have h := congrFun (t.vector_product n p ht hlen a[i.val]!) j
  simp only [Matrix.mul_apply, matrix, Array.getElem!_toList]
  exact h

theorem lift_matrix : matrix 1000 1540 Tables.lifts.rows = U := by
  rw [Tables.lifts_aligned]
  rfl

/-- A first-generator packed row certificate gives exactly its requested matrix row. -/
theorem rowA_of_product (i : Fin 1000)
    (h : Tables.a.product liftRows[i.val]! = Tables.lifts.product D1000.aRows[i.val]!) :
    (U * ambientA) i = (targetA * U) i := by
  rw [← ambientA_packed]
  change (matrix 1000 1540 liftRows.toList * matrix 1540 1540 Tables.a.rows) i = _
  rw [Tables.a.array_mul_row 1000 1540 1540 Tables.a_spec.2 Tables.a_spec.1]
  have hr := Tables.lifts.array_mul_row 1000 1000 1540
    Tables.lifts_spec.2 Tables.lifts_spec.1 D1000.aRows i
  rw [matrix_toList, lift_matrix] at hr
  change (Thompson.BinaryMatrix.decode 1000 D1000.aRows * U) i = _ at hr
  exact (congrArg (vector 1540) h).trans hr.symm

/-- A second-generator packed row certificate gives exactly its requested matrix row. -/
theorem rowB_of_product (i : Fin 1000)
    (h : Tables.b.product liftRows[i.val]! = Tables.lifts.product D1000.bRows[i.val]!) :
    (U * ambientB) i = (targetB * U) i := by
  rw [← ambientB_packed]
  change (matrix 1000 1540 liftRows.toList * matrix 1540 1540 Tables.b.rows) i = _
  rw [Tables.b.array_mul_row 1000 1540 1540 Tables.b_spec.2 Tables.b_spec.1]
  have hr := Tables.lifts.array_mul_row 1000 1000 1540
    Tables.lifts_spec.2 Tables.lifts_spec.1 D1000.bRows i
  rw [matrix_toList, lift_matrix] at hr
  change (Thompson.BinaryMatrix.decode 1000 D1000.bRows * U) i = _ at hr
  exact (congrArg (vector 1540) h).trans hr.symm

theorem matrixA_of_products
    (h : ∀ i : Fin 1000, Tables.a.product liftRows[i.val]! =
      Tables.lifts.product D1000.aRows[i.val]!) : U * ambientA = targetA * U := by
  funext i
  exact rowA_of_product i (h i)

theorem matrixB_of_products
    (h : ∀ i : Fin 1000, Tables.b.product liftRows[i.val]! =
      Tables.lifts.product D1000.bRows[i.val]!) : U * ambientB = targetB * U := by
  funext i
  exact rowB_of_product i (h i)

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining
