module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.MatrixAlgebra
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.TB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.UB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.CB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.UCB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.DB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.C2B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.C3B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.C6B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.C12B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.D2B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.D4B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.D5B

/-!
# Both commutator relations for the literal degree-320b pair

The kernel-checked product chain identifies the two positive source words and
proves their twelfth and fifth powers equal the identity. No group action or
presentation comparison is used. Source: John Bray, ATLAS M24G1-P1.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.CommutatorOrders
open Thompson.BinaryMatrix

theorem commutator_true :
    (matrixA true * matrixB true ^ 2 * matrixA true * matrixB true) ^ 12 = 1 := by
  change ((decode 320 Data.AbRows.toArray) * (decode 320 Data.BbRows.toArray) ^ 2 * (decode 320 Data.AbRows.toArray) * (decode 320 Data.BbRows.toArray)) ^ 12 = 1
  rw [matrixWord12 (decode 320 Data.AbRows.toArray) (decode 320 Data.BbRows.toArray) (decode 320 TBRows.toArray) (decode 320 UBRows.toArray) (decode 320 CBRows.toArray) TB_product UB_product CB_product]
  exact matrixTwelve (decode 320 CBRows.toArray) (decode 320 C2BRows.toArray) (decode 320 C3BRows.toArray) (decode 320 C6BRows.toArray) C2B_product C3B_product C6B_product
    (C12B_product.trans decode_identityPacked)

theorem second_commutator_true :
    (matrixA true * matrixB true ^ 2 * matrixA true * matrixB true ^ 2 *
      matrixA true * matrixB true * matrixA true * matrixB true) ^ 5 = 1 := by
  change ((decode 320 Data.AbRows.toArray) * (decode 320 Data.BbRows.toArray) ^ 2 * (decode 320 Data.AbRows.toArray) * (decode 320 Data.BbRows.toArray) ^ 2 * (decode 320 Data.AbRows.toArray) * (decode 320 Data.BbRows.toArray) * (decode 320 Data.AbRows.toArray) * (decode 320 Data.BbRows.toArray)) ^ 5 = 1
  rw [matrixWord5 (decode 320 Data.AbRows.toArray) (decode 320 Data.BbRows.toArray) (decode 320 TBRows.toArray) (decode 320 UBRows.toArray) (decode 320 CBRows.toArray) (decode 320 UCBRows.toArray) (decode 320 DBRows.toArray) TB_product UB_product CB_product UCB_product DB_product]
  exact matrixFive (decode 320 DBRows.toArray) (decode 320 D2BRows.toArray) (decode 320 D4BRows.toArray) D2B_product D4B_product (D5B_product.trans decode_identityPacked)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.CommutatorOrders
