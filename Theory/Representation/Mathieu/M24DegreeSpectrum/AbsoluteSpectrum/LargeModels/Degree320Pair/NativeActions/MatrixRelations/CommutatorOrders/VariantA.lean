module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.MatrixAlgebra
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.TA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.UA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.CA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.UCA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.DA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.C2A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.C3A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.C6A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.C12A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.D2A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.D4A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Products.D5A

/-!
# Both commutator relations for the literal degree-320a pair

The kernel-checked product chain identifies the two positive source words and
proves their twelfth and fifth powers equal the identity. No group action or
presentation comparison is used. Source: John Bray, ATLAS M24G1-P1.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.CommutatorOrders
open Thompson.BinaryMatrix

theorem commutator_false :
    (matrixA false * matrixB false ^ 2 * matrixA false * matrixB false) ^ 12 = 1 := by
  change ((decode 320 Data.AaRows.toArray) * (decode 320 Data.BaRows.toArray) ^ 2 * (decode 320 Data.AaRows.toArray) * (decode 320 Data.BaRows.toArray)) ^ 12 = 1
  rw [matrixWord12 (decode 320 Data.AaRows.toArray) (decode 320 Data.BaRows.toArray) (decode 320 TARows.toArray) (decode 320 UARows.toArray) (decode 320 CARows.toArray) TA_product UA_product CA_product]
  exact matrixTwelve (decode 320 CARows.toArray) (decode 320 C2ARows.toArray) (decode 320 C3ARows.toArray) (decode 320 C6ARows.toArray) C2A_product C3A_product C6A_product
    (C12A_product.trans decode_identityPacked)

theorem second_commutator_false :
    (matrixA false * matrixB false ^ 2 * matrixA false * matrixB false ^ 2 *
      matrixA false * matrixB false * matrixA false * matrixB false) ^ 5 = 1 := by
  change ((decode 320 Data.AaRows.toArray) * (decode 320 Data.BaRows.toArray) ^ 2 * (decode 320 Data.AaRows.toArray) * (decode 320 Data.BaRows.toArray) ^ 2 * (decode 320 Data.AaRows.toArray) * (decode 320 Data.BaRows.toArray) * (decode 320 Data.AaRows.toArray) * (decode 320 Data.BaRows.toArray)) ^ 5 = 1
  rw [matrixWord5 (decode 320 Data.AaRows.toArray) (decode 320 Data.BaRows.toArray) (decode 320 TARows.toArray) (decode 320 UARows.toArray) (decode 320 CARows.toArray) (decode 320 UCARows.toArray) (decode 320 DARows.toArray) TA_product UA_product CA_product UCA_product DA_product]
  exact matrixFive (decode 320 DARows.toArray) (decode 320 D2ARows.toArray) (decode 320 D4ARows.toArray) D2A_product D4A_product (D5A_product.trans decode_identityPacked)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.CommutatorOrders
