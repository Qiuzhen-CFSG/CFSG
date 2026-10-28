module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Blocks

/-! Checked block 23: actual pivot-column extraction and multiplication by the
supplied inverse. Source and generation are documented in `Rank/Blocks.lean`. -/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
open RowArithmetic


theorem gather_block23 : sourceBlock23.map (gather runs) = minorBlock23 := by decide +kernel

theorem product_block23 : minorBlock23.map (combine pivotInverseRows) = oneBlock23 := by decide +kernel

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
