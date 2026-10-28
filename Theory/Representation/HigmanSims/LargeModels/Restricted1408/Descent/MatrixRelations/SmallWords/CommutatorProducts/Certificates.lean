module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.LongWords.Arithmetic
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.RowsA
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.InverseRows
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ai
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ab
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Comm
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Comm2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Comm4
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ai2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Ab2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Mixed
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Mixed2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Aii
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.Abb
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.SquareComm
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.SquareComm2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Data.SquareComm3

/-!
# Numerical certificates for the three small commutator words

Each equality checks all 1408 rows of the literal published tables. We reuse
`LongPacked`'s simultaneous packed product, whose arithmetic module imports
only `PackedBinaryRows`. Its separate soundness theorem recovers the ordinary
matrix product without assuming any word relation or inverse identity.

The representative full product used about 3.3 GiB peak RSS. Check declarations
sequentially to bound memory, keeping Lean's default thread count and limits.
Source: the retained ATLAS HSG1-P1.M; see `source/README.md`.
-/

set_option Elab.async false

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts.CommutatorCertificate
open LongPacked

theorem a_bounded : BoundedRows aRows := by
  unfold BoundedRows
  decide +kernel

theorem inverse_size : inverseRows.size = 1408 := by decide +kernel

theorem inverse_bounded : BoundedRows inverseRows := by
  unfold BoundedRows
  decide +kernel

theorem ai_size : aiRows.size = 1408 := by decide +kernel

theorem ai_bounded : BoundedRows aiRows := by
  unfold BoundedRows
  decide +kernel

theorem ab_size : abRows.size = 1408 := by decide +kernel

theorem ab_bounded : BoundedRows abRows := by
  unfold BoundedRows
  decide +kernel

theorem comm_size : commRows.size = 1408 := by decide +kernel

theorem comm_bounded : BoundedRows commRows := by
  unfold BoundedRows
  decide +kernel

theorem comm2_size : comm2Rows.size = 1408 := by decide +kernel

theorem comm2_bounded : BoundedRows comm2Rows := by
  unfold BoundedRows
  decide +kernel

theorem comm4_bounded : BoundedRows comm4Rows := by
  unfold BoundedRows
  decide +kernel

theorem ai2_bounded : BoundedRows ai2Rows := by
  unfold BoundedRows
  decide +kernel

theorem ab2_size : ab2Rows.size = 1408 := by decide +kernel

theorem ab2_bounded : BoundedRows ab2Rows := by
  unfold BoundedRows
  decide +kernel

theorem mixed_size : mixedRows.size = 1408 := by decide +kernel

theorem mixed_bounded : BoundedRows mixedRows := by
  unfold BoundedRows
  decide +kernel

theorem mixed2_bounded : BoundedRows mixed2Rows := by
  unfold BoundedRows
  decide +kernel

theorem aii_bounded : BoundedRows aiiRows := by
  unfold BoundedRows
  decide +kernel

theorem abb_size : abbRows.size = 1408 := by decide +kernel

theorem abb_bounded : BoundedRows abbRows := by
  unfold BoundedRows
  decide +kernel

theorem squareComm_size : squareCommRows.size = 1408 := by decide +kernel

theorem squareComm_bounded : BoundedRows squareCommRows := by
  unfold BoundedRows
  decide +kernel

theorem squareComm2_bounded : BoundedRows squareComm2Rows := by
  unfold BoundedRows
  decide +kernel

theorem squareComm3_size : squareComm3Rows.size = 1408 := by decide +kernel

theorem squareComm3_bounded : BoundedRows squareComm3Rows := by
  unfold BoundedRows
  decide +kernel

theorem a_inverse : ProductCertificate aRows inverseRows aiRows := by
  unfold ProductCertificate
  decide +kernel

theorem ai_ab : ProductCertificate aiRows abRows commRows := by
  unfold ProductCertificate
  decide +kernel

theorem comm_comm : ProductCertificate commRows commRows comm2Rows := by
  unfold ProductCertificate
  decide +kernel

theorem comm2_comm2 : ProductCertificate comm2Rows comm2Rows comm4Rows := by
  unfold ProductCertificate
  decide +kernel

theorem comm4_comm : ProductCertificate comm4Rows commRows identityRows := by
  unfold ProductCertificate
  decide +kernel

theorem ai_ai : ProductCertificate aiRows aiRows ai2Rows := by
  unfold ProductCertificate
  decide +kernel

theorem ai2_ab2 : ProductCertificate ai2Rows ab2Rows mixedRows := by
  unfold ProductCertificate
  decide +kernel

theorem mixed_mixed : ProductCertificate mixedRows mixedRows mixed2Rows := by
  unfold ProductCertificate
  decide +kernel

theorem mixed2_mixed : ProductCertificate mixed2Rows mixedRows identityRows := by
  unfold ProductCertificate
  decide +kernel

theorem ai_inverse : ProductCertificate aiRows inverseRows aiiRows := by
  unfold ProductCertificate
  decide +kernel

theorem aii_abb : ProductCertificate aiiRows abbRows squareCommRows := by
  unfold ProductCertificate
  decide +kernel

theorem squareComm_squareComm : ProductCertificate squareCommRows squareCommRows squareComm2Rows := by
  unfold ProductCertificate
  decide +kernel

theorem squareComm2_squareComm : ProductCertificate squareComm2Rows squareCommRows squareComm3Rows := by
  unfold ProductCertificate
  decide +kernel

theorem squareComm3_squareComm3 : ProductCertificate squareComm3Rows squareComm3Rows identityRows := by
  unfold ProductCertificate
  decide +kernel

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts.CommutatorCertificate
