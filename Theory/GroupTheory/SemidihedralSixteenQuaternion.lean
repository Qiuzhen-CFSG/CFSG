module
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic
/-!
# Quaternion centralizers in the semidihedral group of order sixteen

A pair of quaternion generators in the explicit sixteen-element semidirect
product has a common centralizer of order two. The checked pair calculation
uses only sixteen-element group operations, and the presentation equivalence
transports the bound to the standard semidihedral carrier. We also retain the
order of the center of an actual quaternion-eight carrier.

Source application: Aschbacher--Smith, Lemma 2.5.21, terminal quaternion case,
printed p.567.
-/
public section
set_option backward.isDefEq.respectTransparency false
open Subgroup
namespace Semidihedral.QuaternionLocal
private abbrev C8 := Multiplicative (ZMod 8)
private abbrev C2 := Multiplicative (ZMod 2)
private def twist : MulAut C8 where
  toFun x := .ofAdd (3 * x.toAdd)
  invFun x := .ofAdd (3 * x.toAdd)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel
private def action : C2 →* MulAut C8 where
  toFun i := twist ^ i.toAdd.val
  map_one' := rfl
  map_mul' := by intro i j; ext x; revert i j x; decide +kernel
private abbrev D := C8 ⋊[action] C2
private abbrev r : D := SemidirectProduct.inl (.ofAdd 1)
private abbrev s : D := SemidirectProduct.inr (.ofAdd 1)
private instance : Fintype D := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
private theorem d_equiv : Nonempty (D ≃* StandardModel 4 (by omega)) := by
  apply standardModel_equiv_of_presentation (by omega : 4 ≤ 4) r s
  · rw [orderOf_injective _ SemidirectProduct.inl_injective, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one]
    norm_num
  · rw [orderOf_injective _ SemidirectProduct.inr_injective, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one]
  · decide +kernel
  · apply top_le_iff.mp
    intro x _
    have hc : ∀ x : D, ∃ i j : Fin 8, x = r ^ i.val * s ^ j.val := by decide +kernel
    obtain ⟨i, j, rfl⟩ := hc x
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (subset_closure (by simp)) _)
  · rw [SemidirectProduct.card]; simp


private theorem pair_centralizer_bound : ∀ a b : D,
    a ^ 2 = b ^ 2 → a ^ 2 = (a * b) ^ 2 → a ^ 2 ≠ 1 →
    (Finset.univ.filter (fun x : D => x * a = a * x ∧ x * b = b * x)).card = 2 := by
  decide +kernel

private theorem quaternion_center_card : Nat.card (center (QuaternionGroup 2)) = 2 := by
  let e : center (QuaternionGroup 2) ≃ {x : QuaternionGroup 2 // ∀ y, y * x = x * y} :=
    Equiv.subtypeEquivRight (fun x => mem_center_iff)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

private theorem d_quaternion_centralizer (Q : Subgroup D) (e : Q ≃* QuaternionGroup 2) :
    Nat.card (centralizer (Q : Set D)) ≤ 2 := by
  let f := Q.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Q.subtype_injective.comp e.symm.injective
  let a : D := f (.a 1)
  let b : D := f (.xa 0)
  have ha : a ^ 2 ≠ 1 := by
    intro h
    have h' : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = 1 :=
      hf (by simpa only [map_pow, map_one] using h)
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1) h'
  have hab : a ^ 2 = b ^ 2 := by rw [← map_pow, ← map_pow]; congr 1
  have hab' : a ^ 2 = (a * b) ^ 2 := by rw [← map_mul, ← map_pow, ← map_pow]; congr 1
  let T := {x : D // x * a = a * x ∧ x * b = b * x}
  let j : centralizer (Q : Set D) → T := fun x =>
    ⟨x.val, (x.property a (e.symm (.a 1)).property).symm,
      (x.property b (e.symm (.xa 0)).property).symm⟩
  have hi : Function.Injective j := fun x y h => Subtype.ext (show x.val = y.val from congrArg (fun z : T => z.val) h)
  have hc : Nat.card T = 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa only [T, Fintype.card_subtype] using pair_centralizer_bound a b hab hab' ha
  exact (Nat.card_le_card_of_injective j hi).trans hc.le

/-- A quaternion eight in the standard semidihedral sixteen has centralizer
of order at most two. -/
theorem centralizer_card_le_two (Q : Subgroup (StandardModel 4 (by decide)))
    (e : Q ≃* QuaternionGroup 2) : Nat.card (centralizer (Q : Set (StandardModel 4 (by decide)))) ≤ 2 := by
  obtain ⟨d⟩ := d_equiv
  let R := Q.map d.symm.toMonoidHom
  let q := (d.symm.subgroupMap Q).symm.trans e
  have hcent : (centralizer (Q : Set (StandardModel 4 (by decide)))).map d.symm.toMonoidHom =
      centralizer (R : Set D) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      change d.symm z * d.symm y = d.symm y * d.symm z
      exact (d.symm.map_mul z y).symm.trans ((congrArg d.symm (hy z hz)).trans (d.symm.map_mul y z))
    · intro hx
      refine ⟨d x, ?_, d.symm_apply_apply x⟩
      intro z hz
      apply d.symm.injective
      simpa only [map_mul, d.symm_apply_apply] using hx (d.symm z) ⟨z, hz, rfl⟩
  have hh := d_quaternion_centralizer R q
  rw [← hcent, card_map_of_injective d.symm.injective] at hh
  exact hh

/-- The center of any actual quaternion-eight carrier has order two. -/
theorem center_card_of_equiv {Q : Type*} [Group Q] (e : Q ≃* QuaternionGroup 2) :
    Nat.card (center Q) = 2 := by
  exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans quaternion_center_card

end Semidihedral.QuaternionLocal
