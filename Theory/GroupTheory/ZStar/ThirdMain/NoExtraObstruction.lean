module
public import Theory.GroupTheory.ZStar.ThirdMain.ObstructionOrbit
public import Theory.GroupTheory.ZStar.ThirdMain.ObstructionGrowth
public import Theory.Character.ModularBlock.ExactNormalizerSupport
public import Theory.Character.ModularBlock.NoExtraObstruction

/-!
# Compatibility exports for NoExtraObstruction

The reusable principal Brauer argument now lives in
`Theory.Character.ModularBlock.NoExtraObstruction`. This wrapper preserves the historical
Glauberman names and imports for the involution-specific Third Main consumers.
See the Theory module for the mathematical proof and source provenance.
-/

public section
namespace Glauberman.ZStar.BrauerThirdMain

export ModularBlock.BrauerThirdMain
  (not_isExtraObstruction)

end Glauberman.ZStar.BrauerThirdMain
