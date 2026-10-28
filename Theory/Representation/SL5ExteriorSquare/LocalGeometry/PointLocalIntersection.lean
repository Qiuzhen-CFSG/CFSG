module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.FirstNode

/-!
# An order-nine subgroup in the original exterior parabolic intersections

Two commuting cubics act on the disjoint coordinate pairs (0,1) and (3,4),
or (0,1) and (2,3). Their literal matrices embed C3 times C3 in the
intersection of the point parabolic with the three- or four-flag parabolic.
The small checked certificate runs over nine elements, without enumerating
SL5(2). Since the flag subgroup is a two-group, nine divides its relative
index in each intersection.

The original quotient and Sylow transports are in
NaturalSource/Local/Normalizers/JankoMax2Actor. They compare the same
intersection with the max2 actor bound, retaining both original parabolics.
Source: Aschbacher–Smith, 12.5.4, printed p.819/PDF p.836.
-/

public noncomputable section
open Subgroup
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

private def cubic01 : Group :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 1) 1 *
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 5) ≠ 0) 1

private def cubicTail (k : Fin 2) : Group :=
  if k = 0 then
    Matrix.SpecialLinearGroup.transvection (by decide : (3 : Fin 5) ≠ 4) 1 *
      Matrix.SpecialLinearGroup.transvection (by decide : (4 : Fin 5) ≠ 3) 1
  else
    Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 5) ≠ 3) 1 *
      Matrix.SpecialLinearGroup.transvection (by decide : (3 : Fin 5) ≠ 2) 1

private def nineHom (k : Fin 2) : Multiplicative (ZMod 3 × ZMod 3) →* Group where
  toFun u := cubic01 ^ u.toAdd.1.val * cubicTail k ^ u.toAdd.2.val
  map_one' := by revert k; decide +kernel
  map_mul' := by intro u v; revert k u v; decide +kernel

private theorem nineHom_injective (k : Fin 2) : Function.Injective (nineHom k) := by
  revert k
  decide +kernel

private theorem nineHom_mem (k : Fin 2) (u : Multiplicative (ZMod 3 × ZMod 3)) :
    nineHom k u ∈ parabolic 2 ⊓ parabolic (if k = 0 then 3 else 4) := by
  constructor
  · change nineHom k u ∈ parabolic 2
    rw [mem_parabolic_iff_lowerLeft_zero]
    change ∀ i j : Fin 5, 2 ≤ i.val → j.val < 2 → ((nineHom k) u).val i j = 0
    revert k u
    simp only [nineHom, MonoidHom.coe_mk, OneHom.coe_mk]
    decide +kernel
  · change nineHom k u ∈ parabolic (if k = 0 then 3 else 4)
    rw [mem_parabolic_iff_lowerLeft_zero]
    change ∀ i j : Fin 5, (if k = 0 then 3 else 4) ≤ i.val →
      j.val < (if k = 0 then 3 else 4) → ((nineHom k) u).val i j = 0
    revert k u
    simp only [nineHom, MonoidHom.coe_mk, OneHom.coe_mk]
    decide +kernel

/-- The two original coordinate blocks supply an actual order-nine subgroup. -/
theorem nine_dvd_card_point_local_intersection (i : ℕ) (hi : i = 3 ∨ i = 4) :
    9 ∣ Nat.card (parabolic 2 ⊓ parabolic i : Subgroup Group) := by
  suffices hh : ∀ k : Fin 2,
      9 ∣ Nat.card (parabolic 2 ⊓ parabolic (if k = 0 then 3 else 4) : Subgroup Group) by
    rcases hi with rfl | rfl
    · exact hh 0
    · exact hh 1
  intro k
  let f := (nineHom k).codRestrict _ (nineHom_mem k)
  have hf : Function.Injective f := fun x y he => nineHom_injective k (congrArg Subtype.val he)
  have hh := card_dvd_of_injective f hf
  have hc : Nat.card (Multiplicative (ZMod 3 × ZMod 3)) = 9 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa only [hc] using hh

/-- The odd order survives passage to the index of the same flag subgroup. -/
theorem nine_dvd_flag_index_point_local_intersection
    (i : ℕ) (hi : i = 3 ∨ i = 4) :
    9 ∣ flagGroup.relIndex (parabolic 2 ⊓ parabolic i) := by
  let A := parabolic 2 ⊓ parabolic i
  have hp : IsPGroup 2 flagGroup := by
    rw [flagGroup_eq_standardBorel_comap]
    exact BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow.isPGroup'.comap_of_injective
      _ (BinaryLinear.OuterCyclic.slEquivLinear 5).injective
  have hp' : IsPGroup 2 (flagGroup.subgroupOf A) := hp.comap_subtype
  obtain ⟨n,hn⟩ := hp'.exists_card_eq
  have hc := (flagGroup.subgroupOf A).card_mul_index
  rw [hn] at hc
  exact ((show Nat.Coprime 9 2 by decide).pow_right n).dvd_of_dvd_mul_left
    (hc.symm ▸ nine_dvd_card_point_local_intersection i hi)

end Representation.SL5ExteriorSquare
