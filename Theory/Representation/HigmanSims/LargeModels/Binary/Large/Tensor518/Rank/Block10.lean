module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Blocks

/-! Checked block 10: actual pivot-column extraction and multiplication by the
supplied inverse. Source and generation are documented in `Rank/Blocks.lean`. -/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
open RowArithmetic


theorem gather_block10 : sourceBlock10.map (gather runs) = minorBlock10 := by decide +kernel

theorem product_block10 : minorBlock10.map (combine pivotInverseRows) = oneBlock10 := by decide +kernel

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
