module
public import Glauberman.ZStar.ThirdMain.NoExtraObstruction
public import Glauberman.ZStar.ThirdMain.PrimitiveExtraFactor
public import Theory.Character.ModularBlock.PrincipalBrauerEquality

/-!
# Compatibility export for principal subgroup Brauer equality

The equality for every two-subgroup of a finite group is proved in the
Theory layer using the actual principal congruence selectors and coefficient
maps. This wrapper retains the historical Glauberman name and imports used
by the ABG principal-subsection construction; no character enumeration or
involution-specific hypothesis is introduced. See the Theory module for the
maximal-obstruction proof and source provenance.
-/

public section
namespace Glauberman.PrincipalBrauer

export ModularBlock.PrincipalBrauer (subgroupPrincipalBrauerEquality)

end Glauberman.PrincipalBrauer
