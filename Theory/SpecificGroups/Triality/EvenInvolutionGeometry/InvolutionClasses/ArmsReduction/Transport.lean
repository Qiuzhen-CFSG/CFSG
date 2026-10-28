module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction.Collection
/-!
# Transporting the arms shear and square condition to the triality carrier

The checked split-root equation lifts through the elementary embedding and
then descends along the actual quotient. A group equivalence between the two
published arms-radical constructions transports the square relation without
changing any coordinates or action conventions.

Source: Aschbacher–Smith 16.1.4(1), printed p.1171; GLS3 §§2.4–2.6.
-/

public section
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
namespace Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
open Parabolics
noncomputable section
theorem elementary_shear (P : Parameters) (hp : P.prime=2)
    (a : ExtensionField P) (v : ArmsParameters P) :
    shortElementary P hp 0 a * rootElement P hp .arms v * shortElementary P hp 0 a =
      rootElement P hp .arms (shearParameters P a v) := by
  apply elementaryInclusion_injective P
  simpa only [map_mul, shortElementary_val, rootElement_val, armsProduct] using shortSplit_shear P hp a v


theorem short_self_inverse (P : Parameters) (hp : P.prime=2) (a : ExtensionField P) :
    (short P hp 0 a)⁻¹ = short P hp 0 a := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  exact inv_eq_of_mul_eq_one_left ((short_add P hp 0 a a).symm.trans
    ((congrArg (short P hp 0) (CharTwo.add_self_eq_zero a)).trans (short_zero P hp 0)))


theorem short_shear (P : Parameters) (hp : P.prime = 2) (a : ExtensionField P)
    (v : ArmsParameters P) :
    short P hp 0 a * (armsCoordinates P hp v).val * (short P hp 0 a)⁻¹ =
      (armsCoordinates P hp (shearParameters P a v)).val := by
  rw [short_self_inverse P hp a]
  change toCarrier P (shortElementary P hp 0 a) * toCarrier P (rootElement P hp .arms v) *
    toCarrier P (shortElementary P hp 0 a) =
      toCarrier P (rootElement P hp .arms (shearParameters P a v))
  simpa only [map_mul] using congrArg (toCarrier P) (elementary_shear P hp a v)

theorem arms_square_condition (P : Parameters) (hp : P.prime = 2) (v : ArmsParameters P)
    (hs : (armsCoordinates P hp v)^2 = 1) :
    v.2 1 * v.2 0 + armsPairing P (v.1 0) (v.1 1) = 0 := by
  let e := MulEquiv.subgroupCongr (radical_eq_descendedRootSubgroup P hp .arms).symm
  have he : e (armsEquiv P hp v) = armsCoordinates P hp v := rfl
  have hm : e ((armsEquiv P hp v)^2) = 1 := by
    rw [map_pow,he,hs]
  have hs' : (armsEquiv P hp v)^2 = 1 := e.injective (hm.trans (map_one e).symm)
  rw [armsEquiv_square,armsEquiv_central_eq_one_iff] at hs'
  exact hs'
end
end Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
