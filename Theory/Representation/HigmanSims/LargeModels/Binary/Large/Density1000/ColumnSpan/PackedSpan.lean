module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.PackedSpan.Inverse00
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.PackedSpan.Inverse01
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.PackedSpan.Inverse02
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.PackedSpan.Inverse03
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.PackedSpan.Inverse04
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.PackedSpan.Inverse05
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.PackedSpan.Inverse06
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.PackedSpan.Inverse07
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Packed

/-!
# The degree-1000 packed columns span

The shared inverse array, multiplied on the left of the shared packed column
matrix, is the identity. Small kernel-checked intervals establish every row;
the aligned plain tree and the XOR soundness theorem turn them into a matrix
identity. A left inverse then makes the row-vector map surjective.

Both shared column arrays transpose their corresponding matrices in
`Binary/source/density1000.json`. Source: R. A. Wilson et al., ATLAS
HSG1-f2r1000B0; see `PackedSpan/source/README.md` for attribution and checks.
The independent identification of these packed vectors with `columnOrbit`
remains with the column-span assembly owner.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan
open Thompson.BinaryMatrix RowArithmetic

namespace PackedSpan
open RowSpan

/-- The checked intervals exhaust all 1000 rows of the literal inverse product. -/
theorem all_inverse : On 0 1000 Check :=
  ((inverse00.append inverse01).append (inverse02.append inverse03)).append
    ((inverse04.append inverse05).append (inverse06.append inverse07))

/-- The actual shared inverse is a left inverse of the actual packed column matrix. -/
theorem column_inverse :
    decode 1000 Data.columnInverseRows * decode 1000 Data.columnRows = 1 := by
  funext i
  apply decode_product_one_row 1000 Data.columnInverseRows Data.columnRows i columns_size
  rw [← columns_rows, ← columns.product_eq columns_valid]
  exact all_inverse i.val (Nat.zero_le _) i.isLt

end PackedSpan

/-- Unconditional spanning of the literal shared table of packed columns. -/
theorem packedColumns_span :
    Submodule.span (ZMod 2)
      (Set.range (fun i : Fin 1000 => vector 1000 Data.columnRows[i.val]!)) = ⊤ := by
  exact Small.Packed.span_rows_of_inverse Data.columnRows Data.columnInverseRows
    PackedSpan.column_inverse

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan
