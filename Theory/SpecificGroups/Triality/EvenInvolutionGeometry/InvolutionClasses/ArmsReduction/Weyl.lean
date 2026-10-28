module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ShortLeading
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl

/-!
# Weyl normalization of the binary triality arms radical

Two explicit folded Weyl words move the surviving short-root coordinates to
the first central-root layer and move pure long-root elements to the highest
root. Their effects are checked on the twelve positive D₄ roots and transported
through the actual elementary group and central quotient.

Source: Aschbacher–Smith 16.1.4(1), printed p.1171; GLS3 §§2.4–2.6.
-/

public section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
open Parabolics ConcreteBruhat PositiveCoordinates
open RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators

private theorem root_central (i : Fin 8) :
    (rootRepresentative (.sr 1)).val (rootIndex (![4,5,6,7,8,9,10,11] i)) =
      rootIndex (![0,1,2,7,8,9,11,10] i) := by
  rw [rootRepresentative_sr_one]
  change rootReflection 1 (rootIndex (![4,5,6,7,8,9,10,11] i)) = _
  fin_cases i <;>
    simp only [← rootEnumeration_positiveIndex, rootReflection, ← rootEnumeration_reflectionTable]
  all_goals rfl

private theorem root_rotation (i : Fin 5) :
    (rootRepresentative (.r 5)).val (rootIndex (![3,7,8,9,11] i)) =
      rootIndex (![11,2,0,1,10] i) := by
  rw [show (DihedralGroup.r 5 : DihedralGroup 6) = .sr 1 * .sr 0 by decide,
    rootRepresentative_mul, rootRepresentative_sr_one, rootRepresentative_sr_zero]
  change rootReflection 1 (rootReflection 0 (rootReflection 2 (rootReflection 3
    (rootIndex (![3,7,8,9,11] i))))) = _
  fin_cases i <;>
    simp only [← rootEnumeration_positiveIndex, rootReflection, ← rootEnumeration_reflectionTable]
  all_goals rfl

private theorem split_curve_conj (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i j : Fin 12)
    (h : (rootRepresentative w).val (rootIndex i) = rootIndex j) (t : ExtensionField P) :
    splitRepresentative P hp w * curve P i t * (splitRepresentative P hp w)⁻¹ =
      curve P j t := by
  apply Subtype.ext
  change (splitRepresentative P hp w).val * (curve P i t).val *
    (splitRepresentative P hp w).val⁻¹ = (curve P j t).val
  simp only [curve_unit]
  rw [splitRepresentative_rootCurveUnit_conjugation,h]
end Triality.Standard.EvenInvolutionGeometry.ArmsNormalization

namespace Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
open Parabolics ConcreteBruhat PositiveCoordinates
open RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x*y) * g⁻¹ = (g*x*g⁻¹) * (g*y*g⁻¹) := by group

theorem split_central_short_one (P : Parameters) (hp : P.prime = 2) (c : ExtensionField P) :
    splitRepresentative P hp (.sr 1) * shortSplit P 1 c *
      (splitRepresentative P hp (.sr 1))⁻¹ = shortSplit P 0 c := by
  change splitRepresentative P hp (.sr 1) *
    (curve P 4 c * curve P 5 (fieldFrobenius P c) *
      curve P 6 (fieldFrobenius P (fieldFrobenius P c))) *
    (splitRepresentative P hp (.sr 1))⁻¹ =
    curve P 0 c * curve P 1 (fieldFrobenius P c) *
      curve P 2 (fieldFrobenius P (fieldFrobenius P c))
  rw [conjugate_mul,conjugate_mul]
  exact congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (split_curve_conj P hp (.sr 1) 4 0 (root_central 0) c)
      (split_curve_conj P hp (.sr 1) 5 1 (root_central 1) (fieldFrobenius P c)))
    (split_curve_conj P hp (.sr 1) 6 2 (root_central 2) _)

theorem split_rotation_short_two (P : Parameters) (hp : P.prime = 2) (d : ExtensionField P) :
    splitRepresentative P hp (.r 5) * shortSplit P 2 d *
      (splitRepresentative P hp (.r 5))⁻¹ = shortSplit P 0 (fieldFrobenius P d) := by
  change splitRepresentative P hp (.r 5) *
    (curve P 7 d * curve P 8 (fieldFrobenius P d) *
      curve P 9 (fieldFrobenius P (fieldFrobenius P d))) *
    (splitRepresentative P hp (.r 5))⁻¹ =
    curve P 0 (fieldFrobenius P d) * curve P 1 (fieldFrobenius P (fieldFrobenius P d)) *
      curve P 2 (fieldFrobenius P (fieldFrobenius P (fieldFrobenius P d)))
  rw [conjugate_mul,conjugate_mul]
  simp only [fieldFrobenius_three]
  have h := congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (split_curve_conj P hp (.r 5) 7 2 (root_rotation 1) d)
      (split_curve_conj P hp (.r 5) 8 0 (root_rotation 2) (fieldFrobenius P d)))
    (split_curve_conj P hp (.r 5) 9 1 (root_rotation 3) (fieldFrobenius P (fieldFrobenius P d)))
  refine h.trans ?_
  rw [mul_assoc]
  exact ((shortSplit_curves_commute P 0 2 0 d (fieldFrobenius P d)).mul_right
    (shortSplit_curves_commute P 0 2 1 d (fieldFrobenius P (fieldFrobenius P d)))).eq

private theorem split_central_short_two (P : Parameters) (hp : P.prime = 2) (d : ExtensionField P) :
    splitRepresentative P hp (.sr 1) * shortSplit P 2 d *
      (splitRepresentative P hp (.sr 1))⁻¹ = shortSplit P 2 d := by
  change splitRepresentative P hp (.sr 1) *
    (curve P 7 d * curve P 8 (fieldFrobenius P d) *
      curve P 9 (fieldFrobenius P (fieldFrobenius P d))) *
    (splitRepresentative P hp (.sr 1))⁻¹ = _
  rw [conjugate_mul,conjugate_mul]
  exact congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (split_curve_conj P hp (.sr 1) 7 7 (root_central 3) d)
      (split_curve_conj P hp (.sr 1) 8 8 (root_central 4) (fieldFrobenius P d)))
    (split_curve_conj P hp (.sr 1) 9 9 (root_central 5) _)

private theorem carrier_conj_of_split (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (x y : ElementaryGroup P)
    (h : splitRepresentative P hp w * elementaryInclusion P x *
      (splitRepresentative P hp w)⁻¹ = elementaryInclusion P y) :
    weylRepresentative P hp w * toCarrier P x * (weylRepresentative P hp w)⁻¹ =
      toCarrier P y := by
  have he : weylElementary P hp w * x * (weylElementary P hp w)⁻¹ = y := by
    apply elementaryInclusion_injective P
    simpa only [map_mul,map_inv,splitRepresentative] using h
  simpa only [map_mul,map_inv,weylRepresentative] using congrArg (toCarrier P) he

theorem central_short_one (P : Parameters) (hp : P.prime = 2) (c : ExtensionField P) :
    weylRepresentative P hp (.sr 1) * short P hp 1 c *
      (weylRepresentative P hp (.sr 1))⁻¹ = short P hp 0 c := by
  apply carrier_conj_of_split P hp (.sr 1)
  simpa only [shortElementary_val] using split_central_short_one P hp c

theorem central_short_two (P : Parameters) (hp : P.prime = 2) (d : ExtensionField P) :
    weylRepresentative P hp (.sr 1) * short P hp 2 d *
      (weylRepresentative P hp (.sr 1))⁻¹ = short P hp 2 d := by
  apply carrier_conj_of_split P hp (.sr 1)
  simpa only [shortElementary_val] using split_central_short_two P hp d

theorem rotation_short_two (P : Parameters) (hp : P.prime = 2) (d : ExtensionField P) :
    weylRepresentative P hp (.r 5) * short P hp 2 d *
      (weylRepresentative P hp (.r 5))⁻¹ = short P hp 0 (fieldFrobenius P d) := by
  apply carrier_conj_of_split P hp (.r 5)
  simpa only [shortElementary_val] using split_rotation_short_two P hp d

private theorem carrier_long_conj (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i j : Fin 3)
    (h : (rootRepresentative w).val (rootIndex (longPosition i)) = rootIndex (longPosition j))
    (t : fixedField P) :
    weylRepresentative P hp w * long P hp i t * (weylRepresentative P hp w)⁻¹ =
      long P hp j t := by
  apply carrier_conj_of_split P hp w
  simpa only [longElementary_val, longSplit] using
    split_curve_conj P hp w (longPosition i) (longPosition j) h t.val

theorem central_long_one (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    weylRepresentative P hp (.sr 1) * long P hp 1 t *
      (weylRepresentative P hp (.sr 1))⁻¹ = long P hp 2 t :=
  carrier_long_conj P hp (.sr 1) 1 2 (root_central 6) t

theorem central_long_two (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    weylRepresentative P hp (.sr 1) * long P hp 2 t *
      (weylRepresentative P hp (.sr 1))⁻¹ = long P hp 1 t :=
  carrier_long_conj P hp (.sr 1) 2 1 (root_central 7) t

theorem rotation_long_zero (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    weylRepresentative P hp (.r 5) * long P hp 0 t *
      (weylRepresentative P hp (.r 5))⁻¹ = long P hp 2 t :=
  carrier_long_conj P hp (.r 5) 0 2 (root_rotation 0) t

theorem rotation_long_two (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    weylRepresentative P hp (.r 5) * long P hp 2 t *
      (weylRepresentative P hp (.r 5))⁻¹ = long P hp 1 t :=
  carrier_long_conj P hp (.r 5) 2 1 (root_rotation 4) t

theorem highest_commute_short (P : Parameters) (hp : P.prime = 2)
    (t : fixedField P) (i : Fin 3) (a : ExtensionField P) :
    Commute (long P hp 2 t) (short P hp i a) := by
  apply Commute.map
  apply Commute.of_map (elementaryInclusion_injective P)
  simp only [longElementary_val,shortElementary_val]
  exact ((highestCurve_commute P (shortPosition i 0) t.val a).mul_right
    (highestCurve_commute P (shortPosition i 1) t.val (fieldFrobenius P a))).mul_right
      (highestCurve_commute P (shortPosition i 2) t.val (fieldFrobenius P (fieldFrobenius P a)))

theorem highest_commute_long (P : Parameters) (hp : P.prime = 2)
    (t : fixedField P) (i : Fin 3) (a : fixedField P) :
    Commute (long P hp 2 t) (long P hp i a) := by
  apply Commute.map
  apply Commute.of_map (elementaryInclusion_injective P)
  simp only [longElementary_val]
  exact highestCurve_commute P (longPosition i) t.val a.val
end Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
