module

public import Theory.SpecificGroups.Alternating.FiveLocalGeometry
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith

/-!
# Inverting involutions and normalizers of five-subgroups in A₅

A subgroup of order five is Sylow. Its normalizer index divides sixty, is one
modulo five, and is at most twelve; simplicity excludes index one, leaving six.
Thus the normalizer has order ten. The checked pentagon embedding supplies
an involution inverting its rotation subgroup, and Sylow conjugacy transports
that involution and the exact generated normalizer to any five-subgroup.

The final theorem retains an arbitrary actual A₅ isomorphism. It is used for
the component calculation in Aschbacher, *Sporadic Groups* (1994), 47.2,
printed p.261, in the paragraph beginning with Y = P ∩ E(M).
-/

public section

open Subgroup
namespace alternatingGroup.FiveLocalGeometry

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem five_normalizer_ne_top (P : Subgroup A5) (hP : Nat.card P = 5) :
    normalizer (P : Set A5) ≠ ⊤ := by
  intro ht
  rcases (normalizer_eq_top_iff.mp ht).eq_bot_or_eq_top with hb | hb
  · rw [hb, card_bot] at hP
    omega
  · rw [hb, card_top, card] at hP
    omega

/-- The normalizer of every five-subgroup of A₅ has order ten. -/
theorem five_normalizer_card (P : Subgroup A5) (hP : Nat.card P = 5) :
    Nat.card (normalizer (P : Set A5)) = 10 := by
  let N := normalizer (P : Set A5)
  have hle : 5 ≤ Nat.card N := by
    have hd := card_dvd_of_le P.le_normalizer
    rw [hP] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have hi := N.card_mul_index
  rw [card] at hi
  have hb : N.index ≤ 12 := by nlinarith
  have hn : N.index ≠ 1 := fun h => five_normalizer_ne_top P hP (Subgroup.index_eq_one.mp h)
  let S : Sylow 5 A5 := Sylow.ofCard P (by rw [hP, card]; decide +kernel)
  have hs := card_sylow_modEq_one 5 A5
  rw [S.card_eq_index_normalizer] at hs
  change N.index % 5 = 1 % 5 at hs
  change Nat.card N = 10
  generalize N.index = n at *
  interval_cases n <;> omega

private def pentagonRotation : A5 := dihedralHom (.r 1)
private def pentagonReflection : A5 := dihedralHom (.sr 0)

private theorem pentagonRotation_order : orderOf pentagonRotation = 5 := by
  exact (orderOf_injective dihedralHom dihedralHom_injective _).trans
    DihedralGroup.orderOf_r_one

private theorem pentagonReflection_order : orderOf pentagonReflection = 2 := by
  exact (orderOf_injective dihedralHom dihedralHom_injective _).trans
    (DihedralGroup.orderOf_sr _)

private theorem pentagonReflection_conj :
    pentagonReflection * pentagonRotation * pentagonReflection⁻¹ = pentagonRotation⁻¹ := by
  change dihedralHom (.sr 0) * dihedralHom (.r 1) * (dihedralHom (.sr 0))⁻¹ =
    (dihedralHom (.r 1))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
  congr 1

private theorem pentagonReflection_inverts (y : A5) (hy : y ∈ zpowers pentagonRotation) :
    pentagonReflection * y * pentagonReflection⁻¹ = y⁻¹ := by
  obtain ⟨n, rfl⟩ := hy
  have h := map_zpow (MulAut.conj pentagonReflection) pentagonRotation n
  change pentagonReflection * pentagonRotation ^ n * pentagonReflection⁻¹ =
    (pentagonReflection * pentagonRotation * pentagonReflection⁻¹) ^ n at h
  rw [pentagonReflection_conj, inv_zpow] at h
  exact h

private theorem pentagon_normalizer :
    normalizer (zpowers pentagonRotation : Set A5) =
      zpowers pentagonRotation ⊔ zpowers pentagonReflection := by
  have hs : pentagonReflection ∈ normalizer (zpowers pentagonRotation : Set A5) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers (pentagonReflection * pentagonRotation * pentagonReflection⁻¹) = _
    rw [pentagonReflection_conj, zpowers_inv]
  apply Eq.symm
  apply eq_of_le_of_card_ge (sup_le (zpowers pentagonRotation).le_normalizer
    (zpowers_le.mpr hs))
  rw [five_normalizer_card _ (by rw [Nat.card_zpowers, pentagonRotation_order])]
  apply Nat.le_of_dvd Nat.card_pos
  have h₅ := card_dvd_of_le (show zpowers pentagonRotation ≤
    zpowers pentagonRotation ⊔ zpowers pentagonReflection from le_sup_left)
  have h₂ := card_dvd_of_le (show zpowers pentagonReflection ≤
    zpowers pentagonRotation ⊔ zpowers pentagonReflection from le_sup_right)
  rw [Nat.card_zpowers, pentagonRotation_order] at h₅
  rw [Nat.card_zpowers, pentagonReflection_order] at h₂
  exact Nat.lcm_dvd h₅ h₂

/-- A five-subgroup in an actual A₅ has an inverting involution generating its full normalizer. -/
theorem exists_five_normalizer_inverter {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P : Subgroup H) (hP : Nat.card P = 5) :
    ∃ t : H, orderOf t = 2 ∧ (∀ y ∈ P, t * y * t⁻¹ = y⁻¹) ∧
      normalizer (P : Set H) = P ⊔ zpowers t := by
  let P' : Subgroup A5 := P.map e.toMonoidHom
  have hP' : Nat.card P' = 5 := by rw [card_map_of_injective e.injective, hP]
  let S : Sylow 5 A5 := Sylow.ofCard P' (by rw [hP', card]; decide +kernel)
  let R : Sylow 5 A5 := Sylow.ofCard (zpowers pentagonRotation)
    (by rw [Nat.card_zpowers, pentagonRotation_order, card]; decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 S R
  let a : H ≃* A5 := e.trans (MulAut.conj g)
  have ha : P.map a.toMonoidHom = zpowers pentagonRotation := by
    have he := congrArg (fun T : Sylow 5 A5 => (T : Subgroup A5)) hg
    change (P.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at he
    rw [map_map] at he
    exact he
  refine ⟨a.symm pentagonReflection, (a.symm.orderOf_eq _).trans pentagonReflection_order, ?_, ?_⟩
  · intro y hy
    apply a.injective
    have hy' : a y ∈ zpowers pentagonRotation := ha ▸ mem_map.mpr ⟨y, hy, rfl⟩
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using pentagonReflection_inverts (a y) hy'
  · apply (map_injective (f := a.toMonoidHom) a.injective)
    rw [map_equiv_normalizer_eq, ha, pentagon_normalizer, Subgroup.map_sup,
      ha, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

end alternatingGroup.FiveLocalGeometry
