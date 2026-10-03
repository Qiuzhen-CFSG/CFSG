module
public import Theory.GroupTheory.ZStar.ThirdMain.ExtraObstruction
public import Theory.GroupTheory.ZStar.NormalizerBrauerAction
public import Theory.Character.ModularBlock.ObstructionOrbit

/-!
# Compatibility exports for ObstructionOrbit

The reusable principal Brauer argument now lives in
`Theory.Character.ModularBlock.ObstructionOrbit`. This wrapper preserves the historical
Glauberman names and imports for the involution-specific Third Main consumers.
See the Theory module for the mathematical proof and source provenance.
-/

public section
namespace Glauberman.ZStar.BrauerThirdMain

export ModularBlock.BrauerThirdMain
  (normalizerOrbitWitness_of_extraObstruction)

end Glauberman.ZStar.BrauerThirdMain
