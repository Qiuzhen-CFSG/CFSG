module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# Order comparisons for the A₆ specialization of B.5.1

The order 360 separates the A₆ component from the unrelated field and
large binary actors in B.4.2. For the field families, the two-part of the order determines the
field degree. The small endpoints use their checked group orders.

Source: Aschbacher–Smith, B.4.2 and B.5.1, printed pp.86 and 99; the
terminal S₆ branch on p.1155.
The order calculations follow the same formulas used in the unitary-model
sieve in Chapter 13, `FFSections/RankTwo/UnitaryModels.lean`.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation.SixOrders

private theorem sl_card_mul (F : Type*) [Field F] [Finite F]
    (d : ℕ) [NeZero d] :
    Nat.card (Matrix.SpecialLinearGroup (Fin d) F) * (Nat.card F - 1) =
      ∏ i : Fin d, (Nat.card F ^ d - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin d) F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul d

private theorem binary_sub_one_two_part {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ((2 ^ n) ^ k - 1).factorization 2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  have he : ((2 ^ n) ^ k) % 2 = 0 := by
    simp [Nat.pow_mod, Nat.ne_of_gt hn, Nat.ne_of_gt hk]
  have hp : 0 < (2 ^ n) ^ k := by positivity
  omega

private theorem binary_sub_one_pos {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    0 < (2 ^ n) ^ k - 1 := by
  have h : 1 < (2 ^ n) ^ k :=
    one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega)) (by omega)
  omega

private theorem binary_order_two_part {n a b c : ℕ}
    (hn : 0 < n) (hb : 0 < b) (hc : 0 < c) :
    ((2 ^ n) ^ a * ((2 ^ n) ^ b - 1) * ((2 ^ n) ^ c - 1)).factorization 2 = a * n := by
  have hbpos := binary_sub_one_pos hn hb
  rw [Nat.factorization_mul (by positivity) (by
    exact Nat.ne_of_gt (binary_sub_one_pos hn hc)),
    Nat.factorization_mul (by positivity) (Nat.ne_of_gt (binary_sub_one_pos hn hb))]
  simp only [Finsupp.add_apply, binary_sub_one_two_part hn hb,
    binary_sub_one_two_part hn hc, add_zero]
  rw [← pow_mul, Nat.factorization_pow_self Nat.prime_two, Nat.mul_comm]

private theorem sl_three_card (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := sl_card_mul F 3
  change Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) * (q - 1) = _ at h
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  rw [h1, h2] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  rw [h]
  ring

private theorem sl_two_part (F : BinaryField) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)).factorization 2 = F.degree := by
  rw [Atlas.card_sl_two, F.card_eq,
    Nat.factorization_mul (by positivity) (Nat.ne_of_gt (binary_sub_one_pos F.degree_pos (by decide)))]
  simp only [Finsupp.add_apply, binary_sub_one_two_part F.degree_pos (by decide : 0 < 2),
    add_zero, Nat.factorization_pow_self Nat.prime_two]

private theorem sl_three_part (F : BinaryField) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier)).factorization 2 = 3 * F.degree := by
  rw [sl_three_card, F.card_eq]
  exact binary_order_two_part F.degree_pos (by decide) (by decide)

private theorem sp_four_part (F : BinaryField) :
    (Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier)).factorization 2 = 4 * F.degree := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp F.Carrier, F.card_eq]
  exact binary_order_two_part F.degree_pos (by decide) (by decide)

private theorem g2_part (F : BinaryField) :
    (Nat.card (Atlas.G2.Model F.Carrier)).factorization 2 = 6 * F.degree := by
  rw [Atlas.G2.card_Model, F.card_eq]
  exact binary_order_two_part F.degree_pos (by decide) (by decide)

private theorem sl_four_card :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  have h := sl_card_mul (ZMod 2) 4
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.prod_empty, mul_one] at h
  exact h

private theorem sl_five_card :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  have h := sl_card_mul (ZMod 2) 5
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.prod_empty, mul_one] at h
  exact h

private theorem derived_g2_card :
    Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 := by
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

theorem not_sl_two (F : BinaryField) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) ≠ 360 := by
  intro h
  have hp := sl_two_part F
  rw [h, show Nat.factorization 360 2 = 3 by decide +kernel] at hp
  have hn : F.degree = 3 := hp.symm
  rw [Atlas.card_sl_two, F.card_eq, hn] at h
  norm_num at h

theorem not_sl_three (F : BinaryField) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) ≠ 360 := by
  intro h
  have hp := sl_three_part F
  rw [h, show Nat.factorization 360 2 = 3 by decide +kernel] at hp
  have hn : F.degree = 1 := by omega
  rw [sl_three_card, F.card_eq, hn] at h
  norm_num at h

theorem not_sp_four (F : BinaryField) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) ≠ 360 := by
  intro h
  have hp := sp_four_part F
  rw [h, show Nat.factorization 360 2 = 3 by decide +kernel] at hp
  omega

theorem not_g2 (F : BinaryField) : Nat.card (Atlas.G2.Model F.Carrier) ≠ 360 := by
  intro h
  have hp := g2_part F
  rw [h, show Nat.factorization 360 2 = 3 by decide +kernel] at hp
  omega

theorem not_g2_derived : Nat.card (commutator (Atlas.G2.Model (ZMod 2))) ≠ 360 := by
  rw [derived_g2_card]
  decide

theorem not_sl_four : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ≠ 360 := by
  rw [sl_four_card]
  decide

theorem not_sl_five : Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ≠ 360 := by
  rw [sl_five_card]
  decide

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation.SixOrders
