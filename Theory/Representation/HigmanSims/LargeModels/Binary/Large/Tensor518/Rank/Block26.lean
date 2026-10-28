module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Blocks

/-! Checked block 26: actual pivot-column extraction and multiplication by the
supplied inverse. Source and generation are documented in `Rank/Blocks.lean`. -/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
open RowArithmetic


theorem gather_block26 : sourceBlock26.map (gather runs) = minorBlock26 := by decide +kernel

theorem product_block26 : minorBlock26.map (combine pivotInverseRows) = oneBlock26 := by decide +kernel

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
