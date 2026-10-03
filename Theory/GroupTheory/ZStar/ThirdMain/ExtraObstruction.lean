module
public import Theory.Character.ModularBlock.SubgroupPrincipalBrauerData
public import Theory.Character.ModularBlock.PrimitiveCentralIdempotent
public import Theory.Character.ModularBlock.ExtraObstruction

/-!
# Compatibility exports for ExtraObstruction

The reusable principal Brauer argument now lives in
`Theory.Character.ModularBlock.ExtraObstruction`. This wrapper preserves the historical
Glauberman names and imports for the involution-specific Third Main consumers.
See the Theory module for the mathematical proof and source provenance.
-/

public section
namespace Glauberman.ZStar.BrauerThirdMain

export ModularBlock.BrauerThirdMain
  (IsExtraObstruction exists_maximal_extraObstruction)

end Glauberman.ZStar.BrauerThirdMain
