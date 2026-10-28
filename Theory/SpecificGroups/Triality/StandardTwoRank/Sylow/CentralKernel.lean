module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.Tail

/-!
# The first-coordinate kernel in an elementary central-radical subgroup

Suppose an elementary subgroup contains an element with nonzero first
cubic coordinate a. An element in its first-coordinate kernel, with second
coordinate c, commutes with that element. The third-coordinate equation
forces c = t*a for a fixed-field scalar t. Its square and the next
commutation equation give t*Tr(a F(d)) = 0 and
Tr(a F(d)) + t*Norm(a) = 0. Since Norm(a) is nonzero, t vanishes.
Thus the kernel lies in the elementary tail constructed in `Tail`.

This uses the full published multiplication and includes q = 2. Neither
normality nor scalar closure of the elementary subgroup is assumed.
It does not assert that every involution has zero second coordinate.

Source: GLS3 2.4.5(b)(4) and §2.6 (`refs/KGroup/GLS3/chapter2.tex`);
the triality rank calculation used on printed p.356 of `refs/quasithin.pdf`.
-/

public section

open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.Parabolics
open Triality.Standard.Parabolics.CentralRootSquare
open Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage
namespace Triality.Standard.TwoRank
noncomputable section

theorem fixed_ratio_of_higherCoefficient_eq_zero (P : Parameters) (hp : P.prime = 2)
    {a c : ExtensionField P} (ha : a ≠ 0) (h : higherCoefficient P a c = 0) :
    ∃ t : fixedField P, c = t.val * a := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have he : a * fieldFrobenius P c = fieldFrobenius P a * c :=
    CharTwo.add_eq_zero.mp h
  refine ⟨⟨c / a, ?_⟩, (div_mul_cancel₀ c ha).symm⟩
  change fieldFrobenius P (c / a) = c / a
  rw [map_div₀]
  apply (div_eq_div_iff ((map_ne_zero _).mpr ha) ha).mpr
  calc
    fieldFrobenius P c * a = a * fieldFrobenius P c := mul_comm _ _
    _ = fieldFrobenius P a * c := he
    _ = c * fieldFrobenius P a := mul_comm _ _

theorem armsPairing_fixed_mul_left (P : Parameters) (t : fixedField P)
    (a d : ExtensionField P) :
    armsPairing P (t.val * a) d = t * armsPairing P a d := by
  apply Subtype.ext
  have ht : fieldFrobenius P t.val = t.val := t.property
  simp only [armsPairing_coe, Subfield.coe_mul, map_mul, ht]
  ring

theorem trace_norm_multiple (P : Parameters) (hp : P.prime = 2)
    (t : fixedField P) (a : ExtensionField P) :
    cubicTrace P (t.val * a * fieldFrobenius P a *
      fieldFrobenius P (fieldFrobenius P a)) = t * cubicNorm P a := by
  convert cubicTrace_fixed P hp (t * cubicNorm P a) using 2
  simp only [Subfield.coe_mul, cubicNorm]
  ring

theorem central_kernel_scalar_obstruction (P : Parameters) (hp : P.prime = 2)
    {a c d : ExtensionField P} (ha : a ≠ 0)
    (hhigher : higherCoefficient P a c = 0)
    (hsquare : armsPairing P c d = 0)
    (hcomm : armsPairing P a d +
      cubicTrace P (c * fieldFrobenius P a * fieldFrobenius P (fieldFrobenius P a)) = 0) :
    c = 0 := by
  obtain ⟨t, rfl⟩ := fixed_ratio_of_higherCoefficient_eq_zero P hp ha hhigher
  rw [armsPairing_fixed_mul_left] at hsquare
  rw [trace_norm_multiple P hp] at hcomm
  have hN : cubicNorm P a ≠ 0 := by
    intro h
    have hz : a * fieldFrobenius P a * fieldFrobenius P (fieldFrobenius P a) = 0 :=
      congrArg Subtype.val h
    exact mul_ne_zero (mul_ne_zero ha ((map_ne_zero _).mpr ha))
      ((map_ne_zero _).mpr ((map_ne_zero _).mpr ha)) hz
  have ht : t = 0 := by
    by_contra ht
    have hpair := (mul_eq_zero.mp hsquare).resolve_left ht
    rw [hpair, zero_add] at hcomm
    exact mul_ne_zero ht hN hcomm
  simp [ht]

private theorem coordinates_zero (P : Parameters) (hp : P.prime = 2) :
    coordinates P hp (0, 0) = 1 := by
  apply Subtype.ext
  rw [coordinates_val, rootElement_factorization]
  simp [extendOrbit]

private theorem second_eq_zero_of_multiply (P : Parameters) (hp : P.prime = 2)
    (v w : RootOrbitParameters P .central)
    (hv : v.1 0 ≠ 0) (hw : w.1 0 = 0)
    (hs : multiply P w w = (0, 0))
    (he : multiply P v w = multiply P w v) : w.1 1 = 0 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  apply central_kernel_scalar_obstruction P hp (d := w.1 2) hv
  · have ht : v.1 2 + w.1 2 + higherCoefficient P (w.1 0) (v.1 1) =
        w.1 2 + v.1 2 + higherCoefficient P (v.1 0) (w.1 1) :=
      congrArg (fun z : RootOrbitParameters P .central => z.1 2) he
    simp only [hw, higherCoefficient, map_zero, zero_mul, add_zero] at ht
    change higherCoefficient P (v.1 0) (w.1 1) = 0
    unfold higherCoefficient
    linear_combination -ht
  · have ht := congrArg (fun z : RootOrbitParameters P .central => z.2 1) hs
    simpa [multiply, hw, higherCoefficient, CharTwo.add_self_eq_zero,
      -fieldFrobenius_apply] using ht
  · have ht := congrArg (fun z : RootOrbitParameters P .central => z.2 0) he
    simp only [multiply, Matrix.cons_val_zero, hw, armsPairing_zero_left,
      map_zero, mul_zero, zero_mul, add_zero] at ht
    linear_combination -ht

/-- An involution with zero first coordinate that commutes with an element
with nonzero first coordinate also has zero second coordinate. -/
theorem second_eq_zero_of_square_eq_one_of_commute (P : Parameters) (hp : P.prime = 2)
    (v w : RootOrbitParameters P .central)
    (hv : v.1 0 ≠ 0) (hw : w.1 0 = 0)
    (hsquare : (coordinates P hp w) ^ 2 = 1)
    (hcomm : Commute (coordinates P hp v) (coordinates P hp w)) : w.1 1 = 0 := by
  have he : multiply P v w = multiply P w v :=
    (coordinates P hp).injective ((coordinates_multiply P hp v w).trans
      (hcomm.eq.trans (coordinates_multiply P hp w v).symm))
  have hs : multiply P w w = (0, 0) :=
    (coordinates P hp).injective ((coordinates_multiply P hp w w).trans
      ((pow_two (coordinates P hp w)).symm.trans
        (hsquare.trans (coordinates_zero P hp).symm)))
  exact second_eq_zero_of_multiply P hp v w hv hw hs he

/-- The kernel conclusion for an arbitrary actual elementary subgroup. This
is the first-coordinate kernel used by the central-radical cardinality bound. -/
theorem central_elementary_kernel_mem_tail (P : Parameters) (hp : P.prime = 2)
    (E : Subgroup (radical P .central)) [IsElementaryAbelian 2 E]
    (r k : radical P .central) (hr : r ∈ E) (hk : k ∈ E)
    (hr0 : (firstLayer P hp r).1 ≠ 0) (hk0 : (firstLayer P hp k).1 = 0) :
    k ∈ (tailRadicalHom P hp).range := by
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hcomm : Commute r k := by
    show r * k = k * r
    exact congrArg (fun z : E => z.val) (mul_comm (⟨r, hr⟩ : E) ⟨k, hk⟩)
  have hsq : k ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian k hk
  obtain ⟨v, rfl⟩ := (coordinates P hp).surjective r
  obtain ⟨w, rfl⟩ := (coordinates P hp).surjective k
  rw [firstLayer_coordinates] at hr0 hk0
  change v.1 0 ≠ 0 at hr0
  change w.1 0 = 0 at hk0
  have hw1 := second_eq_zero_of_square_eq_one_of_commute P hp v w hr0 hk0 hsq hcomm
  refine ⟨Multiplicative.ofAdd (w.1 2, w.2), ?_⟩
  change coordinates P hp (tailParameters P (w.1 2, w.2)) = coordinates P hp w
  apply congrArg (coordinates P hp)
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [tailParameters, hk0, hw1]
  · rfl
end
end Triality.Standard.TwoRank
