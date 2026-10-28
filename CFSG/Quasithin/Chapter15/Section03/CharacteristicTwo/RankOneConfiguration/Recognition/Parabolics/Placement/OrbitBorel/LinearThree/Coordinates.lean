module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree.Transport

/-!
# Product coordinates required by the linear-three orbit calculation

This is an output contract for the two-component quotient construction.
It retains an actual surjection, its two-group kernel, an identification
of the selected component with the first factor, two genuine PSL₃(2)
models, and an automorphism exchanging the factors and preserving the
image of the specified subgroup. The product of the marked Sylow two
subgroups normalizes that same image. No order-two condition is imposed
on the exchanging automorphism.

Neither existence of these coordinates nor the invariant-subgroup
contradiction is asserted here. Those are independent proof obligations.
The source assembly must construct the coordinates on the actual S-span
and use the actual Y₊ subgroup, as in Aschbacher–Smith, proof of 15.3.27,
printed p.1130 (PDF p.1147, combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree
universe u

/-- The geometric output of the two-component quotient construction.
All invariance fields refer to the image under the same surjection. -/
structure ProductCoordinates {H : Type u} [Group H] (L Y : Subgroup H) where
  First : Type u
  Second : Type u
  [firstGroup : Group First]
  [secondGroup : Group Second]
  [firstFinite : Finite First]
  [secondFinite : Finite Second]
  firstModel : ClassicalGroup.IsPSL First 3 2
  secondModel : ClassicalGroup.IsPSL Second 3 2
  quotient : H →* First × Second
  surjective : Function.Surjective quotient
  kernel_two : IsPGroup 2 quotient.ker
  first_image : L.map quotient = (⊤ : Subgroup First).prod (⊥ : Subgroup Second)
  firstSylow : Sylow 2 First
  secondSylow : Sylow 2 Second
  sylow_invariant : (firstSylow : Subgroup First).prod (secondSylow : Subgroup Second) ≤
    normalizer (Y.map quotient : Set (First × Second))
  exchange : MulAut (First × Second)
  exchange_first : ((⊤ : Subgroup First).prod (⊥ : Subgroup Second)).map
    exchange.toMonoidHom = (⊥ : Subgroup First).prod (⊤ : Subgroup Second)
  exchange_second : ((⊥ : Subgroup First).prod (⊤ : Subgroup Second)).map
    exchange.toMonoidHom = (⊤ : Subgroup First).prod (⊥ : Subgroup Second)
  exchange_invariant : (Y.map quotient).map exchange.toMonoidHom = Y.map quotient

attribute [instance] ProductCoordinates.firstGroup ProductCoordinates.secondGroup
  ProductCoordinates.firstFinite ProductCoordinates.secondFinite

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree
