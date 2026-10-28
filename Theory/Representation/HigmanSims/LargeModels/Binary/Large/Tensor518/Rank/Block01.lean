module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Blocks

/-! Checked block 1: actual pivot-column extraction and multiplication by the
supplied inverse. Source and generation are documented in `Rank/Blocks.lean`. -/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
open RowArithmetic


theorem gather_block1 : sourceBlock1.map (gather runs) = minorBlock1 := by decide +kernel

theorem product_block1 : minorBlock1.map (combine pivotInverseRows) = oneBlock1 := by decide +kernel

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
