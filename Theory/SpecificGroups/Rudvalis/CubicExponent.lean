module
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal.Three
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.GroupTheory.PGroup.OrderTwentySeven
public import Theory.GroupTheory.PGroup.SylowCubeExponent
import all Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal.Three

/-!
# Exponent three in the concrete Rudvalis group

Cubing is a homomorphism on the certified nonabelian subgroup of order 27.
Its three word coordinates have cube one, so the whole subgroup has exponent
three. The actual group order makes it Sylow, excluding nine from every
element order in Ru. The internal import deliberately extends the existing
word certificate, using its private coverage proof without repeating the
degree-4060 computations or exposing those helpers.

Source: GLS3 Table 5.3r, p.279, and Aschbacher--Smith 4.3.16, p.618.
ATLAS attribution and the original action convention are retained in the
imported `Multiplier.OddLocal.Three` certificate.
-/

open Subgroup
namespace Rudvalis.Multiplier.OddLocal.ThreeCertificate
attribute [local irreducible] x y z

/-- The original certified order-27 subgroup has exponent three. -/
public theorem cube_eq_one (g : P) : g ^ 3 = 1 := by
  let f := OrderTwentySeven.cubeHom card_P not_isMulCommutative_P
  have hx : f ⟨x,x_mem⟩ = 1 := by
    rw [OrderTwentySeven.cubeHom_apply]; exact Subtype.ext x_cube
  have hy : f ⟨y,y_mem⟩ = 1 := by
    rw [OrderTwentySeven.cubeHom_apply]; exact Subtype.ext y_cube
  have hz : f ⟨z,z_mem⟩ = 1 := by
    rw [OrderTwentySeven.cubeHom_apply]; exact Subtype.ext z_cube
  obtain ⟨i,hi⟩ := reps_surjective g
  have he : g = (⟨x,x_mem⟩ : P) ^ i.1.val * (⟨y,y_mem⟩ : P) ^ i.2.1.val *
      (⟨z,z_mem⟩ : P) ^ i.2.2.val := Subtype.ext hi.symm
  rw [←OrderTwentySeven.cubeHom_apply card_P not_isMulCommutative_P]
  change f g = 1
  rw [he,map_mul,map_mul,map_pow,map_pow,map_pow,hx,hy,hz]
  simp only [one_pow,mul_one]

end Rudvalis.Multiplier.OddLocal.ThreeCertificate

namespace Rudvalis
open Multiplier.OddLocal.ThreeCertificate

/-- Nine divides no element order in the original degree-4060 ATLAS carrier. -/
public theorem not_nine_dvd_orderOf (x : Model) : ¬ 9 ∣ orderOf x := by
  have hp : IsPGroup 3 P := IsPGroup.of_card (n := 3) card_P
  have hi : ¬ 3 ∣ P.index := by
    intro hi
    have hd := Nat.mul_dvd_mul (dvd_refl (Nat.card P)) hi
    rw [P.card_mul_index,card_P,model_card] at hd
    norm_num at hd
  exact Subgroup.not_nine_dvd_orderOf_of_sylow_cube (hp.toSylow hi) cube_eq_one x

end Rudvalis
