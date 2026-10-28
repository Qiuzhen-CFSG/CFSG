module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Ahat6Cubic
public import Theory.GroupTheory.CharacteristicCoreCenter

/-!
# The central preimage in an exceptional triple-cover block

The central cubic norm on the original commutator module is zero. A vector
fixed by the preimage of the quotient center is fixed by a central element
of order three, so this norm equals that vector and it must be trivial.
The same preimage is solvable: its two-core kernel is nilpotent and its
quotient embeds in the center of the block quotient.

These are the two exact inputs used to exclude the exceptional triple-six
block in 14.6.10(5), printed p.1029, using C.1.22, printed p.129.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
variable {K : Type*} [Group K]

/-- The central preimage fixes no nonidentity vector of the original U. -/
theorem IsExceptionalAhat6Block.fixed_coreCenter_eq_one (h : IsExceptionalAhat6Block K) (v : blockU K)
    (hv : (v : K) ∈ Subgroup.centralizer (Subgroup.upperCentralSeriesStep (pCore 2 K) : Set K)) : v = 1 := by
  let := h.1.finite
  let := h.1.elementary
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (K ⧸ pCore 2 K)) 3
    (by rw [h.2.2.1])
  have hne : (z : K ⧸ pCore 2 K) ≠ 1 := by
    intro he
    have he' : z = 1 := Subtype.ext he
    rw [he',orderOf_one] at hz
    contradiction
  have hz3 : (z : K ⧸ pCore 2 K) ^ 3 = 1 :=
    congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)
  let w : Additive (blockU K) := Additive.ofMul v
  have hfix : uRepresentation h.1 z w = w := by
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z.val
    have hkC : k ∈ Subgroup.upperCentralSeriesStep (pCore 2 K) := by
      rw [Subgroup.upperCentralSeriesStep_eq_comap_center]
      change QuotientGroup.mk' (pCore 2 K) k ∈ center _
      rw [hk]
      exact z.property
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [←hk,uRepresentation_apply]
    change k * (v : K) * k⁻¹ = (v : K)
    rw [hv k hkC,mul_inv_cancel_right]
  have he := LinearMap.congr_fun (central_cubic_quadratic h z z.property hne hz3) w
  change uRepresentation h.1 z (uRepresentation h.1 z w) + uRepresentation h.1 z w + w = 0 at he
  rw [hfix,hfix] at he
  have hw2 : w + w = 0 := by
    calc
      w + w = (2 : ZMod 2) • w := (two_smul (ZMod 2) w).symm
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide,zero_smul]
  rw [hw2,zero_add] at he
  exact congrArg Additive.toMul he

/-- The central preimage above the two-core of a short group is solvable. -/
theorem IsShort.coreCenter_solvable (h : IsShort K) :
    Group.IsSolvable (Subgroup.upperCentralSeriesStep (pCore 2 K)) := by
  let := h.finite
  let N := Subgroup.upperCentralSeriesStep (pCore 2 K)
  let q := QuotientGroup.mk' (pCore 2 K)
  have hQN : pCore 2 K ≤ N := by
    rw [show N = Subgroup.upperCentralSeriesStep (pCore 2 K) from rfl,
      Subgroup.upperCentralSeriesStep_eq_comap_center]
    intro x hx
    change q x ∈ center _
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
    rw [hxq]
    exact one_mem _
  let f : N →* center (K ⧸ pCore 2 K) := (q.comp N.subtype).codRestrict _ (by
    intro n
    have hn : (n : K) ∈ Subgroup.upperCentralSeriesStep (pCore 2 K) := n.property
    rw [Subgroup.upperCentralSeriesStep_eq_comap_center] at hn
    exact hn)
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  exact Group.isSolvable_of_ker_le_range (inclusion hQN) f (by
    intro n hn
    have he : q (n : K) = 1 := congrArg Subtype.val hn
    exact ⟨⟨n,(QuotientGroup.eq_one_iff _).mp he⟩,rfl⟩)
end CFSG.Quasithin.ChapterC
