module
public import Theory.Character.ModularBlock.PrincipalPrimitivity

/-!
# Primitivity identifies the involution Brauer selector

For a finite group and its principal congruence-block data, the compatible
local principal selector has nonzero product with the involution Brauer image.
The local selector is already centrally primitive. If the Brauer image is
also centrally primitive, the two selectors are equal: their nonzero central
idempotent product is a factor of both and hence equals both.

This assembles the specialized endpoints of
`c3503435:glauberman_zStar/Submission/ZStar/CentralPrimitiveFactor.lean`.
The generic factor-collapse lemmas stay in the reusable modular-block layer
and are re-exported here with their historical short names. The assumption
of Brauer-image primitivity is retained; no unconditional equality is claimed.
-/

public section
namespace Glauberman.ZStar.CentralPrimitiveFactor
open ModularBlock
export ModularBlock.CentralPrimitiveFactor
  (eq_of_mul_eq_left_of_right_isCentrallyPrimitive
    eq_of_mul_ne_zero_of_both_isCentrallyPrimitive)

variable {G : Type*} [Group G] [Finite G]

/-- Primitivity of the involution Brauer image identifies it with the local selector. -/
theorem localPrincipalBlockElementInAmbientResidue_eq_involutionBrauer_of_primitive
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1)
    (hBrauerPrimitive : IsCentrallyPrimitive
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z)) :
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) =
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z := by
  exact eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
    (BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
      d (Subgroup.centralizer ({z} : Set G))) hBrauerPrimitive
    (CompatibleBrauerBlock.localPrincipalBlockElement_mul_involutionBrauer_ne_zero d z hz)

/-- The same comparison packaged as the principal-Brauer equality predicate. -/
theorem involutionPrincipalBrauerEquality_of_brauer_isCentrallyPrimitive
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1)
    (hBrauerPrimitive : IsCentrallyPrimitive
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z)) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  exact localPrincipalBlockElementInAmbientResidue_eq_involutionBrauer_of_primitive
    d z hz hBrauerPrimitive

end Glauberman.ZStar.CentralPrimitiveFactor
