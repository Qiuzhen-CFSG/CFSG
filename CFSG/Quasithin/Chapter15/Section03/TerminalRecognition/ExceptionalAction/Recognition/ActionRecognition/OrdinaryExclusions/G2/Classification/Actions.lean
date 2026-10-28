module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Selecting the natural G₂ action from the full B.5.1 conclusion

The component of order 6048 has two-part 32. The checked order formulas
exclude each other field family in B.4.2 and each repeated-natural case
of B.5.1. The exceptional permutation and triple-cover actors have
different orders. In the surviving binary G₂ case the marked actor has
order 12096, so an ambient actor of order at most 12096 is that actor.
Its actual intertwiner therefore identifies the whole section action.

No replacement of the moved section by the original module is made.
The elementary order arithmetic follows the existing A₇ specialization
in `TerminalRecognition/Cases/MarkedElimination/AlternatingSevenDimension/Orders.lean`.
Source: Aschbacher–Smith, B.4.2 and B.5.1, printed pp.86 and 99, applied
in the final proof of 15.3.1, printed p.1155.
-/

public section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.Classification
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

private theorem not_sl_two (F : BinaryField) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) ≠ 6048 := by
  intro h
  have hp := sl_two_part F
  rw [h, show Nat.factorization 6048 2 = 5 by decide +kernel] at hp
  rw [Atlas.card_sl_two, F.card_eq, ← hp] at h
  norm_num at h

private theorem not_sl_three (F : BinaryField) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) ≠ 6048 := by
  intro h
  have hp := sl_three_part F
  rw [h, show Nat.factorization 6048 2 = 5 by decide +kernel] at hp
  omega

private theorem not_sp_four (F : BinaryField) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) ≠ 6048 := by
  intro h
  have hp := sp_four_part F
  rw [h, show Nat.factorization 6048 2 = 5 by decide +kernel] at hp
  omega

private theorem not_g2 (F : BinaryField) : Nat.card (Atlas.G2.Model F.Carrier) ≠ 6048 := by
  intro h
  have hp := g2_part F
  rw [h, show Nat.factorization 6048 2 = 5 by decide +kernel] at hp
  omega

private theorem alt_card_ne {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    Nat.card (alternatingGroup (Fin n)) ≠ 6048 := by
  rcases hn with rfl | rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] <;>
    norm_num [Nat.factorial]

private theorem eq_card_of_equiv {A B : Type*} [Group A] [Group B]
    (h : Nat.card A = 6048) (e : A ≃* B) : Nat.card B = 6048 :=
  (Nat.card_congr e.toEquiv).symm.trans h

private theorem not_binary_linear {A : Type*} [Group A] (hA : Nat.card A = 6048)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  have h := eq_card_of_equiv hA e
  rcases hn with rfl | rfl
  · rw [sl_four_card] at h; omega
  · rw [sl_five_card] at h; omega

variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]

private theorem marked_g2_natural (ρ : Representation (ZMod 2) D W)
    {L J : Subgroup D} (hD : Nat.card D ≤ 12096)
    (e : MarkedActionEquiv ρ J L (g2Natural (ZMod 2))
      (commutator (Atlas.G2.Model (ZMod 2)))) :
    Nonempty (ActionEquiv ρ (g2Natural (ZMod 2))) := by
  have hJ : Nat.card J = 12096 := by
    rw [Nat.card_congr e.action.groupEquiv.toEquiv, Atlas.G2.card_Model]
    norm_num
  have ht : J = ⊤ := J.eq_top_of_card_eq (by
    exact le_antisymm J.card_le_card_group (hJ ▸ hD))
  subst J
  exact ⟨{ groupEquiv := Subgroup.topEquiv.symm.trans e.action.groupEquiv
           linearEquiv := e.action.linearEquiv
           intertwines := fun g v => e.action.intertwines ⟨g, mem_top g⟩ v }⟩

/-- The complete irreducible list selects the actual full G₂ natural action. -/
theorem irreducible_natural (ρ : Representation (ZMod 2) D W)
    {L J : Subgroup D} (hD : Nat.card D ≤ 12096) (hL : Nat.card L = 6048)
    (h : IrreducibleActionCase ρ L J) :
    Nonempty (ActionEquiv ρ (g2Natural (ZMod 2))) := by
  cases h with
  | linearTwo F _ e _ _ => exact (not_sl_two F (eq_card_of_equiv hL e.groupEquiv)).elim
  | linearThree F _ e _ => exact (not_sl_three F (eq_card_of_equiv hL e.groupEquiv)).elim
  | symplectic F _ _ e _ => exact (not_sp_four F (eq_card_of_equiv hL e.groupEquiv)).elim
  | symplecticTwo e _ =>
    exact (alt_card_ne (by omega : 6 = 5 ∨ 6 = 6 ∨ 6 = 7 ∨ 6 = 8)
      (eq_card_of_equiv hL (e.subgroupEquiv.trans binarySymplecticDerivedEquiv))).elim
  | g2 F _ _ e _ _ => exact (not_g2 F (eq_card_of_equiv hL e.groupEquiv)).elim
  | g2Two e _ _ => exact marked_g2_natural ρ hD e
  | symmetric n hn e _ _ =>
    exact (alt_card_ne (by omega) (eq_card_of_equiv hL e.subgroupEquiv)).elim
  | alternatingSix _ e _ _ =>
    exact (alt_card_ne (by omega) (eq_card_of_equiv hL e.groupEquiv)).elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (alt_card_ne (by omega) (eq_card_of_equiv hL e)).elim
  | tripleSix _ a _ =>
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    rw [hL, Nat.card_congr a.quotientEquiv.toEquiv,
      Nat.card_congr a.centerEquiv.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd] at hc
  | binaryLinear n hn _ e _ => exact (not_binary_linear hL hn e.groupEquiv).elim
  | orthogonalSix _ _ e _ _ =>
    exact (alt_card_ne (by omega) (eq_card_of_equiv hL e.groupEquiv)).elim
  | symmetricEight _ e _ =>
    exact (alt_card_ne (by omega) (eq_card_of_equiv hL e.subgroupEquiv)).elim
  | exteriorFive _ _ e _ _ _ =>
    have hc := eq_card_of_equiv hL e
    rw [sl_five_card] at hc
    omega

/-- Every B.5.1 action branch is compared on the literal central section. -/
theorem section_natural (ρ : Representation (ZMod 2) D W)
    {L : Subgroup D} {s : MovedSection ρ L}
    (hD : Nat.card D ≤ 12096) (hL : Nat.card L = 6048)
    (h : QuasisimpleActionCase ρ L s) :
    Nonempty (ActionEquiv s.action (g2Natural (ZMod 2))) := by
  cases h with
  | irreducible _ _ _ source _ => exact irreducible_natural s.action hD hL source
  | doubleThree F _ e _ _ => exact (not_sl_three F (eq_card_of_equiv hL e.groupEquiv)).elim
  | naturalDual n hn _ e => exact (not_binary_linear hL hn e.some.groupEquiv).elim
  | repeatedNatural n r hn _ _ _ e => exact (not_binary_linear hL hn e.some.groupEquiv).elim
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.Classification
