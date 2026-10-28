module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Mathlib.Data.Nat.Multiplicity

/-!
# Group comparisons for the symplectic moved section

The literal Sp₄ order is q⁴(q⁴−1)(q²−1). Comparing two-parts and cancelling
odd factors distinguishes it from all variable-field competitors in B.4.2,
and recovers the field cardinality in the surviving row. The remaining
small rows have order at most 20160, except SL₅(2), whose two-part is 2¹⁰.

The order arithmetic follows the sibling SL₃ and G₂ comparison proofs;
the group orders come from their attributed matrix and octonion imports.
Source: Aschbacher–Smith B.4.2, B.5.1, B.5.6 and 13.6.19, printed
pp.86, 99, 105 and 931 of the combined manuscript of 1 March 2004.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection

private theorem odd_factor {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ¬ 2 ∣ (2 ^ n) ^ k - 1 := by
  have hm : (2 ^ n) ^ k % 2 = 0 := by
    simp [Nat.pow_mod, Nat.ne_of_gt hn, Nat.ne_of_gt hk]
  have hp : 0 < (2 ^ n) ^ k := pow_pos (pow_pos (by decide) _) _
  omega

private theorem two_part {a b u v : ℕ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b := by
  have he := congrArg (emultiplicity 2) h
  simp only [Nat.prime_two.emultiplicity_mul, Nat.prime_two.emultiplicity_pow_self,
    emultiplicity_eq_zero.mpr hu, emultiplicity_eq_zero.mpr hv, add_zero] at he
  exact_mod_cast he

/-- Cancellation after taking the two-part recovers both parameters in the
rank-two order shape used by SL₃, Sp₄ and G₂. -/
private theorem equal_order_parameters {n m a b : ℕ}
    (hn : 0 < n) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (h : (2 ^ n) ^ a * ((2 ^ n) ^ a - 1) * ((2 ^ n) ^ 2 - 1) =
      (2 ^ m) ^ b * ((2 ^ m) ^ b - 1) * ((2 ^ m) ^ 2 - 1)) :
    n = m ∧ a = b := by
  have he : n * a = m * b := two_part
    (Nat.prime_two.not_dvd_mul (odd_factor hn ha) (odd_factor hn (by decide : 0 < 2)))
    (Nat.prime_two.not_dvd_mul (odd_factor hm hb) (odd_factor hm (by decide : 0 < 2)))
    (by simpa only [pow_mul, mul_assoc] using h)
  have hfield : (2 ^ n) ^ a = (2 ^ m) ^ b := by simp only [← pow_mul, he]
  have hq : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
  have hp : 0 < (2 ^ n) ^ a * ((2 ^ n) ^ a - 1) :=
    Nat.mul_pos (by positivity) (Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hq))
  rw [← hfield] at h
  have hc := Nat.eq_of_mul_eq_mul_left hp h
  have hsq : (2 ^ n) ^ 2 = (2 ^ m) ^ 2 := by
    have h1 : 0 < (2 ^ n) ^ 2 := by positivity
    have h2 : 0 < (2 ^ m) ^ 2 := by positivity
    omega
  have heq : n = m := Nat.pow_right_injective (by decide : 2 ≤ 2)
    (Nat.pow_left_injective (by decide : 2 ≠ 0) hsq)
  refine ⟨heq, Nat.eq_of_mul_eq_mul_left hn ?_⟩
  rwa [← heq] at he

private theorem not_sl_two {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (2 ^ n) ^ 4 * ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 2 - 1) ≠
      2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  intro h
  have he : n * 4 = m := two_part
    (Nat.prime_two.not_dvd_mul (odd_factor hn (by decide : 0 < 4))
      (odd_factor hn (by decide : 0 < 2)))
    (odd_factor hm (by decide : 0 < 2)) (by simpa only [pow_mul, mul_assoc] using h)
  have hq : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
  have hx : 1 < (2 ^ n) ^ 4 := Nat.one_lt_pow (by decide) hq
  have hy : (2 ^ n) ^ 2 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hfield : 2 ^ m = (2 ^ n) ^ 4 := by rw [← he, pow_mul]
  rw [hfield, mul_assoc] at h
  have hc := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2 ^ n) ^ 4) h
  have hxsub : (2 ^ n) ^ 4 - 1 + 1 = (2 ^ n) ^ 4 := Nat.sub_add_cancel (by omega)
  have hsqsub : ((2 ^ n) ^ 4) ^ 2 - 1 + 1 = ((2 ^ n) ^ 4) ^ 2 :=
    Nat.sub_add_cancel (Nat.le_of_lt (Nat.one_lt_pow (by decide) hx))
  have hlt : ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 2 - 1) <
      ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 4 + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  nlinarith only [hc, hxsub, hsqsub, hlt]


private theorem card_sp_reordered (F : Type*) [Field F] [Finite F] :
    Nat.card (Sp F) = Nat.card F ^ 4 * (Nat.card F ^ 4 - 1) * (Nat.card F ^ 2 - 1) := by
  rw [card_sp]
  ring

variable {F : Type*} [Field F] [Finite F] {m : ℕ}

/-- All fixed small rows are smaller than Sp₄(4). -/
theorem card_gt_small (hF : Nat.card F = 2 ^ m) (hm : 1 < m) :
    20160 < Nat.card (Sp F) := by
  rw [card_sp_reordered]
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ m by omega)
  have hle := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
  exact lt_of_lt_of_le (by norm_num : 20160 < 4 ^ 4 * (4 ^ 4 - 1) * (4 ^ 2 - 1)) hle

/-- The rank-one odd part is incompatible with the symplectic order. -/
theorem not_linearTwo (hF : Nat.card F = 2 ^ m) (hm : 0 < m)
    (E : BinaryField) : ¬ Nonempty (Sp F ≃* SL(2, E.Carrier)) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  rw [card_sp_reordered, Atlas.card_sl_two, hF, E.card_eq] at h
  exact not_sl_two hm E.degree_pos h

/-- The SL₃ comparison uses its genuine cover, including its center. -/
theorem not_linearThree (hF : Nat.card F = 2 ^ m) (hm : 0 < m)
    (E : BinaryField) : ¬ Nonempty (Sp F ≃* SL(3, E.Carrier)) := by
  rintro ⟨e⟩
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(3,E.Carrier))
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] at hc
  have hc' := hc.trans (Matrix.PSL3.LinearThree.card_projective_mul_scalar E.Carrier)
  have h := Nat.card_congr e.toEquiv
  rw [card_sp_reordered, hc', hF, E.card_eq] at h
  have he := (equal_order_parameters hm E.degree_pos (by decide) (by decide) h).2
  omega

/-- The octonion G₂ model has a different leading exponent. -/
theorem not_g2 (hF : Nat.card F = 2 ^ m) (hm : 0 < m)
    (E : BinaryField) : ¬ Nonempty (Sp F ≃* Atlas.G2.Model E.Carrier) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  rw [card_sp_reordered, Atlas.G2.card_Model, hF, E.card_eq] at h
  have he := (equal_order_parameters hm E.degree_pos (by decide) (by decide) h).2
  omega

/-- An actual symplectic group isomorphism recovers the field cardinality. -/
theorem field_card (hF : Nat.card F = 2 ^ m) (hm : 0 < m)
    (E : BinaryField) (e : Sp F ≃* Sp E.Carrier) : Nat.card E.Carrier = Nat.card F := by
  have h := Nat.card_congr e.toEquiv
  rw [card_sp_reordered, card_sp_reordered, hF, E.card_eq] at h
  have he := (equal_order_parameters hm E.degree_pos (by decide) (by decide) h).1
  rw [hF, E.card_eq, he]

private theorem sl_card_mul (E : Type*) [Field E] [Finite E]
    (d : ℕ) [NeZero d] :
    Nat.card (Matrix.SpecialLinearGroup (Fin d) E) * (Nat.card E - 1) =
      ∏ i : Fin d, (Nat.card E ^ d - Nat.card E ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin d) E)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul d

/-- SL₄(2) is too small; SL₅(2) has incompatible two-part. -/
theorem not_binary_linear (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    {d : ℕ} (hd : d = 4 ∨ d = 5) : ¬ Nonempty (Sp F ≃* SL(d, ZMod 2)) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  rcases hd with rfl | rfl
  · have hs := sl_card_mul (ZMod 2) 4
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at hs
    have hl := card_gt_small hF hm
    omega
  · have hs := sl_card_mul (ZMod 2) 5
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at hs
    rw [card_sp_reordered, hF] at h
    have he : m * 4 = 10 := two_part
      (Nat.prime_two.not_dvd_mul (odd_factor (by omega : 0 < m) (by decide : 0 < 4))
        (odd_factor (by omega : 0 < m) (by decide : 0 < 2)))
      (by norm_num : ¬ 2 ∣ 9765)
      (by simpa [pow_mul, mul_assoc] using h.trans hs)
    omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection
