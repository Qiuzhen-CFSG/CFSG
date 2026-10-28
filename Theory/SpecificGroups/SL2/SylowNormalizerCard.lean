module
public import Theory.SpecificGroups.SL2.EvenBorelResidual
/-!
# The order of the actual even-field rank-one Sylow normalizer

The prescribed Sylow maps to the corresponding projective Sylow, whose
normalizer is the actual affine Borel. In characteristic two the projective
map is an isomorphism, so its order is q(q-1). This supplies the odd divisor
for the selected Cartan in Aschbacher--Smith 10.2.3(4), pp.746--747.
-/
public section
open Subgroup BenderSuzuki.Converse
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "D" => SL(2,F)
theorem card_sylow_normalizer_even (P : Sylow 2 D) :
    Nat.card (normalizer ((P : Subgroup D) : Set D)) = Nat.card F * (Nat.card F - 1) := by
  let Q := P.mapSurjective (f := pi F) (pi_surjective (F := F))
  rw [Nat.card_congr (equivMapOfInjective (normalizer ((P : Subgroup D) : Set D)) (pi F)
    (pi_injective (F := F))).toEquiv]
  rw [map_normalizer_eq_of_bijective (P : Subgroup D)
    ⟨pi_injective (F := F), pi_surjective (F := F)⟩]
  change Nat.card (normalizer ((Q : Subgroup PSL(2,F)) : Set PSL(2,F))) = _
  simpa only [Sylow.coe_coe] using
    (Nat.card_congr (ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F Q).toEquiv).trans
      (ProjectiveSpecialLinearGroup.EvenBorelResidual.card_borel F)

end Matrix.SpecialLinearGroup
