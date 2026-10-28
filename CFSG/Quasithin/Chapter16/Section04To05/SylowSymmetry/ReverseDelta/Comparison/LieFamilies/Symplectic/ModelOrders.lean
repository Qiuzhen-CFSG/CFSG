module

public import Theory.SpecificGroups.SymplecticFour.FieldComponent
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Orders of the symplectic outer residual models

The derived half-field group is simple and nonsolvable, including the
binary endpoint A₆. Its order exceeds that of SL₂ over the full field:
for half-field order q > 2 compare q⁴(q²−1)(q⁴−1) with q²(q⁴−1),
and at q = 2 compare 360 with 60. For odd degree, Sz(q) has order
(q²+1)q²(q−1), which exceeds q(q²−1). The order formulas and model
identifications are proved in the imported intrinsic group modules.

Source: the field and graph-field rows of Aschbacher–Smith 16.1.4(4),(7),
printed p.1171, used in 16.4.11(2), p.1193 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.SymplecticModelOrders
open Subgroup Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms.GraphFieldFixedResidual
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

theorem derived_not_solvable {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ m) :
    ¬ Group.IsSolvable (commutator (Sp F)) := by
  let := FieldComponent.derived_isSimple hm hF
  let : Nontrivial (Sp F) := (commutator (Sp F)).subtype_injective.nontrivial
  by_cases hb : m = 1
  · have htwo : Nat.card F = 2 := by simpa [hb] using hF
    let e := Binary.derivedEquivAlternatingSix htwo
    let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    intro h
    let := h
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · have hq : 2 < Nat.card F := by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) (by omega))
    let := perfect_of_card_gt_two hq
    let e : commutator (Sp F) ≃* Sp F :=
      (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans topEquiv
    intro h
    let := h
    exact Group.IsPerfect.not_isSolvable (Sp F)
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

theorem derived_field_card_gt {F K : Type*}
    [Field F] [Finite F] [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ (2 * m))
    (hK : Nat.card K = 2 ^ m) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) < Nat.card (commutator (Sp K)) := by
  rw [Atlas.card_sl_two, hF]
  by_cases hb : m = 1
  · have htwo : Nat.card K = 2 := by simpa [hb] using hK
    rw [Nat.card_congr (Binary.derivedEquivAlternatingSix htwo).toEquiv,
      nat_card_alternatingGroup]
    norm_num [hb]
  · have hq : 2 < Nat.card K := by
      rw [hK]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) (by omega))
    let := perfect_of_card_gt_two hq
    rw [Group.IsPerfect.commutator_eq_top,
      Nat.card_congr (topEquiv : (⊤ : Subgroup (Sp K)) ≃* Sp K).toEquiv, card_sp, hK]
    have hpow : 2 ^ (2 * m) = (2 ^ m) ^ 2 := by rw [Nat.mul_comm 2 m, pow_mul]
    rw [hpow]
    let q := 2 ^ m
    have hq' : 2 < q := by simpa only [hK] using hq
    change q ^ 2 * ((q ^ 2) ^ 2 - 1) < q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1)
    rw [show (q ^ 2) ^ 2 = q ^ 4 by ring]
    have hq2 : 1 < q ^ 2 := by nlinarith
    have hq4 : 1 < q ^ 4 := by nlinarith [sq_nonneg (q ^ 2)]
    apply Nat.mul_lt_mul_of_pos_right _ (by omega : 0 < q ^ 4 - 1)
    have hs : 0 < q ^ 2 - 1 := by omega
    have h24 : q ^ 2 < q ^ 4 := by nlinarith [sq_nonneg (q ^ 2)]
    exact h24.trans_le (Nat.le_mul_of_pos_right _ hs)

theorem suzuki_card_gt {F : Type*} [Field F] [Finite F]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2 ^ (2 * m + 1)) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) < Nat.card (SuzukiMatrixGroup m) := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) :=
    iterateFrobeniusEquiv_def K 2 (m + 1)
  have hc := (BenderSuzuki.External.huppert_blackburn_XI_3_3 m hm pi hpi).2.2.2.2.2.2.1
  rw [Atlas.card_sl_two, hF, hc]
  let q := 2 ^ (2 * m + 1)
  have hq : 2 ≤ q := Nat.le_self_pow (by omega) 2
  change q * (q ^ 2 - 1) < (q ^ 2 + 1) * q ^ 2 * (q - 1)
  have hs : 0 < q - 1 := by omega
  have he : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, Nat.add_mul, one_mul, ← pow_two]
    have : 1 ≤ q ^ 2 := by nlinarith
    omega
  rw [he, ← mul_assoc]
  apply Nat.mul_lt_mul_of_pos_right _ hs
  have hh : q + 1 < q ^ 2 + 1 := by nlinarith
  calc
    q * (q + 1) < q * (q ^ 2 + 1) := Nat.mul_lt_mul_of_pos_left hh (by omega)
    _ ≤ q ^ 2 * (q ^ 2 + 1) := Nat.mul_le_mul_right _ (by nlinarith)
    _ = (q ^ 2 + 1) * q ^ 2 := Nat.mul_comm _ _

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.SymplecticModelOrders
