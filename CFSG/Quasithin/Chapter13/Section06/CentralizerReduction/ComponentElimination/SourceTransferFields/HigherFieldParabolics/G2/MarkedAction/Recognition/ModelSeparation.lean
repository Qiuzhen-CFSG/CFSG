module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ModelContract
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Mathlib.Data.Nat.Multiplicity

/-!
# Actual group separation for the higher-field G₂ action

The orders of the literal octonion automorphism and matrix groups distinguish
all variable-field competitors of G₂ in B.4.2 and B.5.1. Taking the two-part
first identifies the leading powers of the field sizes. For SL₃ and Sp₄,
cancellation then identifies their squared field sizes, which contradicts
the different leading exponents. For SL₂ the remaining odd factors differ
strictly. The same argument recovers the field size from the order of G₂.
Finally G₂(4) already has order 251596800, above every fixed binary row.

This constructs the complete `ModelSeparation` input for the exhaustive B.5
comparison on the actual marked component; no group-family label, module
recognition, or simplicity assumption enters these comparisons.

Source: Aschbacher–Smith, B.4.2 and B.5.1, printed pp.86 and 99, used before
13.6.14 and in 13.6.19, pp.929–931. The uniform order counts are the cited
lower-layer theorems, including the attributed ATLAS octonion calculation.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
open ChapterB.QuasisimpleSource

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
    (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) ≠
      2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  intro h
  have he : n * 6 = m := two_part
    (Nat.prime_two.not_dvd_mul (odd_factor hn (by decide : 0 < 6))
      (odd_factor hn (by decide : 0 < 2)))
    (odd_factor hm (by decide : 0 < 2)) (by simpa only [pow_mul, mul_assoc] using h)
  have hq : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
  have hx : 1 < (2 ^ n) ^ 6 := Nat.one_lt_pow (by decide) hq
  have hy : (2 ^ n) ^ 2 ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hfield : 2 ^ m = (2 ^ n) ^ 6 := by rw [← he, pow_mul]
  rw [hfield, mul_assoc] at h
  have hc := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2 ^ n) ^ 6) h
  have hxsub : (2 ^ n) ^ 6 - 1 + 1 = (2 ^ n) ^ 6 := Nat.sub_add_cancel (by omega)
  have hsqsub : ((2 ^ n) ^ 6) ^ 2 - 1 + 1 = ((2 ^ n) ^ 6) ^ 2 :=
    Nat.sub_add_cancel (Nat.le_of_lt (Nat.one_lt_pow (by decide) hx))
  have hlt : ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) <
      ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 6 + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  nlinarith only [hc, hxsub, hsqsub, hlt]

private theorem card_sl_three (E : BinaryField) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) E.Carrier) =
      Nat.card E.Carrier ^ 3 * (Nat.card E.Carrier ^ 3 - 1) *
        (Nat.card E.Carrier ^ 2 - 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) E.Carrier))
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] at h
  exact h.trans (Matrix.PSL3.LinearThree.card_projective_mul_scalar E.Carrier)

/-- Every higher-field octonion automorphism model satisfies all five group
comparisons required by the exhaustive source B.5 action sieve. -/
theorem modelSeparation_of_degree_gt_one (F : BinaryField) (hF : 1 < F.degree) :
    ModelSeparation F where
  not_linearTwo E := by
    rintro ⟨e⟩
    have h := Nat.card_congr e.toEquiv
    rw [Atlas.G2.card_Model, Atlas.card_sl_two, F.card_eq, E.card_eq] at h
    exact not_sl_two F.degree_pos E.degree_pos h
  not_linearThree E := by
    rintro ⟨e⟩
    have h := Nat.card_congr e.toEquiv
    rw [Atlas.G2.card_Model, card_sl_three, F.card_eq, E.card_eq] at h
    have he := (equal_order_parameters F.degree_pos E.degree_pos
      (by decide) (by decide) h).2
    omega
  not_symplecticFour E := by
    rintro ⟨e⟩
    have h := Nat.card_congr e.toEquiv
    rw [Atlas.G2.card_Model, Theory.SpecificGroups.SymplecticFour.card_sp,
      F.card_eq, E.card_eq] at h
    have hr : (2 ^ E.degree) ^ 4 * ((2 ^ E.degree) ^ 2 - 1) *
        ((2 ^ E.degree) ^ 4 - 1) =
      (2 ^ E.degree) ^ 4 * ((2 ^ E.degree) ^ 4 - 1) *
        ((2 ^ E.degree) ^ 2 - 1) := by ring
    rw [hr] at h
    have he := (equal_order_parameters F.degree_pos E.degree_pos
      (by decide) (by decide) h).2
    omega
  large_order := by
    rw [Atlas.G2.card_Model]
    have hq : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ F.degree by omega)
    have hle := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    exact lt_of_lt_of_le (by norm_num : 9999360 < 4 ^ 6 * (4 ^ 6 - 1) * (4 ^ 2 - 1)) hle
  field_order E := by
    rintro ⟨e⟩
    have h := Nat.card_congr e.toEquiv
    rw [Atlas.G2.card_Model, Atlas.G2.card_Model, E.card_eq, F.card_eq] at h
    have he := (equal_order_parameters E.degree_pos F.degree_pos
      (by decide) (by decide) h).1
    rw [E.card_eq, F.card_eq, he]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
