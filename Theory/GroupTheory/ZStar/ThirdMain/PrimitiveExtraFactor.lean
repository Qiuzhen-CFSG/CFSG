module
public import Theory.GroupTheory.ZStar.ThirdMain.NonprincipalFactor
public import Theory.Character.ModularBlock.PrimitiveExtraFactor

/-!
# Compatibility exports for PrimitiveExtraFactor

The reusable principal Brauer argument now lives in
`Theory.Character.ModularBlock.PrimitiveExtraFactor`. This wrapper preserves the historical
Glauberman names and imports for the involution-specific Third Main consumers.
See the Theory module for the mathematical proof and source provenance.
-/

public section
namespace Glauberman.ZStar.BrauerThirdMain

export ModularBlock.BrauerThirdMain
  (exists_primitiveExtraFactor_of_centralIdempotent)

end Glauberman.ZStar.BrauerThirdMain
