module

public import Theory.SpecificGroups.MinusExtraspecial.Recognition
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic

/-!
# Cubic fixed points determine the extraspecial group of order 32

A three-group acting on an extraspecial group of order 32 with fixed subgroup
exactly the center forces the quaternion–quaternion central-product type.
The minus type has twelve elements with square one, whereas the fixed set
has two. Orbit counting modulo three excludes that type. The remaining
rank branch supplies an elementary eight and hence the two quaternion factors.

This uses the explicit quaternion–dihedral model only for a 32-element
square calculation, and preserves the actual subgroup embeddings in the
conclusion. Source application: Aschbacher–Smith, I.4.6, printed p.417;
Aschbacher, “A 2-local characterization of M12”, Illinois J. Math. 47 (2003).
-/

open Subgroup MulAction

namespace Theory.GroupAction

private theorem minus_square_one_card :
    Nat.card {x : MinusExtraspecial.Model // x ^ 2 = 1} = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- A three-group with precisely central fixed points forces the plus-type
quaternion factorization; the type is proved, rather than assumed. -/
public theorem quaternionCentralProduct_of_three_fixed_center {A P : Type*} [Group A] [Group P] [Finite P]
    [MulDistribMulAction A P] [IsExtraspecial 2 P]
    (hA : IsPGroup 3 A) (hP : Nat.card P = 32)
    (hfixed : ∀ u : P, (∀ a : A, a • u = u) ↔ u ∈ center P) :
    Nonempty (QuaternionCentralProductData P) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S := {u : P // u ^ 2 = 1}
  let : MulAction A S := {
    smul a u := ⟨a • (u : P), by rw [← smul_pow', u.property, smul_one]⟩
    one_smul u := Subtype.ext (one_smul A (u : P))
    mul_smul a b u := Subtype.ext (mul_smul a b (u : P)) }
  let e : fixedPoints A S ≃ center P := {
    toFun u := ⟨u.val.val, (hfixed _).mp (fun a => congrArg Subtype.val (u.property a))⟩
    invFun u := ⟨⟨u, by
      have hs := congrArg Subtype.val (pow_card_eq_one' (x := u))
      simpa only [IsExtraspecial.center_order_p 2 P, SubmonoidClass.coe_pow,
        OneMemClass.coe_one] using hs⟩,
      fun a => Subtype.ext ((hfixed _).mpr u.property a)⟩
    left_inv u := rfl
    right_inv u := rfl }
  have hmod := hA.card_modEq_card_fixedPoints S
  rw [Nat.card_congr e, IsExtraspecial.center_order_p 2 P] at hmod
  rcases IsExtraspecial.rank_two_or_normal_elementary_eight_of_card_thirty_two hP with
    hrank | ⟨E, hEn, hEe, hE, hZE⟩
  · obtain ⟨f⟩ := IsExtraspecial.exists_mulEquiv_minusExtraspecial_model hrank hP
    have hS : Nat.card S = 12 := by
      let eS : S ≃ {x : MinusExtraspecial.Model // x ^ 2 = 1} :=
        f.toEquiv.subtypeEquiv (fun x => by
          change x ^ 2 = 1 ↔ (f x) ^ 2 = 1
          rw [← map_pow, f.map_eq_one_iff])
      exact (Nat.card_congr eS).trans minus_square_one_card
    rw [hS] at hmod
    norm_num [Nat.ModEq] at hmod
  · let : E.Normal := hEn
    let : IsElementaryAbelian 2 E := hEe
    obtain ⟨B, C, hB, hC, hspan, hinter, hcomm⟩ :=
      exists_quaternion_factors_of_extraspecial_thirty_two_elementary hP E hE hZE
    exact ⟨⟨B, C, hB, hC, hinter, hcomm, hspan⟩⟩

end Theory.GroupAction
