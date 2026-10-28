module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Blocks

/-! Checked block 16: actual pivot-column extraction and multiplication by the
supplied inverse. Source and generation are documented in `Rank/Blocks.lean`. -/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
open RowArithmetic


theorem gather_block16 : sourceBlock16.map (gather runs) = minorBlock16 := by decide +kernel

theorem product_block16 : minorBlock16.map (combine pivotInverseRows) = oneBlock16 := by decide +kernel

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
