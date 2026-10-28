module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Inverse00
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Inverse01
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Inverse02
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Inverse03
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Inverse04
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Inverse05
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Inverse06
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Inverse07

/-!
# The literal degree-1000 row inverse identity

The interval certificates cover all the required source indices. Their kernel
checks refer to the unchanged source tables. See `RowSpan/source/README.md`
for the proof structure, measurements and ATLAS attribution.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan

open Thompson.BinaryMatrix

/-- All rows of the proposed left inverse have been checked. -/
theorem all_inverse : On 0 1000 InverseCheck :=
  (((inverse00.append inverse01).append (inverse02.append inverse03)).append ((inverse04.append inverse05).append (inverse06.append inverse07)))

/-- The unchanged JSON row inverse is a left inverse of the candidate row matrix. -/
theorem row_inverse : decode 1000 Data.rowInverseRows * decode 1000 Data.rowRows = 1 := by
  funext i
  apply RowArithmetic.decode_product_one_row 1000 Data.rowInverseRows Data.rowRows i rowsTree_size
  rw [← rowsTree_rows, ← rowsTree.product_eq rowsTree_valid]
  exact all_inverse i.val (Nat.zero_le _) i.isLt

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan
