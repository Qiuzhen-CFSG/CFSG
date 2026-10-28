module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Elements.D0
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Elements.D1
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Elements.Y

/-!
# Relations of the right support in the J₃ affine configuration

The two literal generators have cube one, their product and inverse product
have fifth power one, and the marked element is a commutator word in them.
Every equation is checked on all 6156 letters using the certified packed maps.
The four power relations will kill both generators in the abelianization.

Source: the affine local in GLS3 Table 5.3h, printed p.269; the configuration
used for Aschbacher--Smith A.2.19 and I.2.1. The discovery data in the parent
`source/right-support-discovery.json` are not proof premises.
-/

namespace Sporadic.Janko3.ThreeCoverConfig.RightCertificate
open Theory.GroupTheory OrderCertificate
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option Elab.async false

public theorem d0Perm_cube : d0Perm ^ 3 = 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem d1Perm_cube : d1Perm ^ 3 = 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem d0_cube : d0 ^ 3 = 1 := by
  apply Subtype.ext
  change (d0 : Equiv.Perm (Fin 6156)) ^ 3 = 1
  rw [← d0Perm_eq]
  exact d0Perm_cube

public theorem d1_cube : d1 ^ 3 = 1 := by
  apply Subtype.ext
  change (d1 : Equiv.Perm (Fin 6156)) ^ 3 = 1
  rw [← d1Perm_eq]
  exact d1Perm_cube

public theorem product_fifth : (d0 * d1) ^ 5 = 1 := by
  apply Subtype.ext
  change ((d0 : Equiv.Perm (Fin 6156)) * d1) ^ 5 = 1
  rw [← d0Perm_eq, ← d1Perm_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem inverseProduct_fifth : (d0⁻¹ * d1) ^ 5 = 1 := by
  apply Subtype.ext
  change ((d0 : Equiv.Perm (Fin 6156))⁻¹ * d1) ^ 5 = 1
  rw [← d0Perm_eq, ← d1Perm_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem y_eq_word : y = d1 * d0⁻¹ * d1⁻¹ * d0 := by
  apply Subtype.ext
  change (y : Equiv.Perm (Fin 6156)) =
    (d1 : Equiv.Perm (Fin 6156)) * (d0 : Equiv.Perm (Fin 6156))⁻¹ *
      (d1 : Equiv.Perm (Fin 6156))⁻¹ * d0
  rw [← yPerm_eq, ← d0Perm_eq, ← d1Perm_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem d0Perm_square : d0Perm * d0Perm = d0Perm⁻¹ :=
  eq_inv_of_mul_eq_one_left (by simpa only [pow_succ, pow_zero, one_mul] using d0Perm_cube)

public theorem d1Perm_square : d1Perm * d1Perm = d1Perm⁻¹ :=
  eq_inv_of_mul_eq_one_left (by simpa only [pow_succ, pow_zero, one_mul] using d1Perm_cube)

end Sporadic.Janko3.ThreeCoverConfig.RightCertificate
