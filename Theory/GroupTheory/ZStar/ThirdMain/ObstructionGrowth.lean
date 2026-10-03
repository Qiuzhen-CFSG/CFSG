module
public import Theory.GroupTheory.ZStar.ThirdMain.ExtraObstruction
public import Theory.GroupTheory.ZStar.ThirdMain.PrimitiveExtraFactor
public import Theory.Character.ModularBlock.NormalizerSupportGrowth
public import Theory.Character.ModularBlock.ObstructionGrowth

/-!
# Compatibility exports for ObstructionGrowth

The reusable principal Brauer argument now lives in
`Theory.Character.ModularBlock.ObstructionGrowth`. This wrapper preserves the historical
Glauberman names and imports for the involution-specific Third Main consumers.
See the Theory module for the mathematical proof and source provenance.
-/

public section
namespace Glauberman.ZStar.BrauerThirdMain

export ModularBlock.BrauerThirdMain
  (exists_larger_extraObstruction_of_strict_normalizer_support)

end Glauberman.ZStar.BrauerThirdMain
