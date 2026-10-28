module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismReduction
public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Coarse odd automorphism bounds from the Frattini quotient

The quotient has dimension at most four. Counting its general linear group
proves that odd automorphism subgroup orders divide 315, or 21 below core
order 32. In particular the three-part already has the required sharp bound.
The missing structural inputs are precisely exclusion of primes five and
seven; this module does not assert those exclusions or the final theorem.
-/

namespace SmallNonabelianTwoGroup

open scoped IsMulCommutative

public theorem card_mulAut_elementary_two_pow
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (dimension : ℕ) (hcard : Nat.card E = 2 ^ dimension) :
    Nat.card (MulAut E) =
      ∏ index : Fin dimension, (2 ^ dimension - 2 ^ index.val) := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2 ^ dimension := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod, hcard] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive E) = dimension :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let autLinear : MulAut E ≃* (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let basis := Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hdim
  let coordinates := autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive E)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' basis).symm)
  rw [Nat.card_congr coordinates.toEquiv, Matrix.card_GL_field]
  simp only [ZMod.card]

public theorem exists_frattini_quotient_dimension_le_four
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32) :
    ∃ dimension : ℕ, dimension ≤ 4 ∧ Nat.card (Q ⧸ frattini Q) = 2 ^ dimension := by
  obtain ⟨dimension, hdimension⟩ := (htwo.to_quotient (frattini Q)).exists_card_eq
  have hhalf := frattini_quotient_card_le_half htwo hnoncomm
  refine ⟨dimension, ?_, hdimension⟩
  by_contra hnot
  have hpower : 2 ^ 5 ≤ 2 ^ dimension :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [← hdimension] at hpower
  norm_num at hpower
  omega

public theorem odd_actor_card_dvd_coarse
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32)
    (actor : Subgroup (MulAut Q)) (hodd : Odd (Nat.card actor)) :
    Nat.card actor ∣ (if Nat.card Q = 32 then 315 else 21) := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  obtain ⟨dimension, hdim, hdimension⟩ :=
    exists_frattini_quotient_dimension_le_four htwo hnoncomm hbound
  have hhalf := frattini_quotient_card_le_half htwo hnoncomm
  have hdiv := Subgroup.card_dvd_of_injective
    ((Subgroup.quotientAut (frattini Q)).comp actor.subtype)
    (odd_frattini_action_injective htwo actor hodd)
  rw [card_mulAut_elementary_two_pow (Q ⧸ frattini Q) dimension hdimension] at hdiv
  have hlift (hsmall : Nat.card actor ∣ 21) :
      Nat.card actor ∣ (if Nat.card Q = 32 then 315 else 21) := by
    split_ifs
    · exact hsmall.trans (by norm_num)
    · exact hsmall
  interval_cases dimension
  · apply hlift
    norm_num [Fin.prod_univ_succ] at hdiv
    simp [hdiv]
  · apply hlift
    norm_num [Fin.prod_univ_succ] at hdiv
    simp [hdiv]
  · apply hlift
    norm_num [Fin.prod_univ_succ] at hdiv
    have hthree : Nat.card actor ∣ 3 :=
      hodd.coprime_two_right.dvd_of_dvd_mul_left hdiv
    exact hthree.trans (by norm_num)
  · apply hlift
    norm_num [Fin.prod_univ_succ] at hdiv
    exact (hodd.coprime_two_right.pow_right 3).dvd_of_dvd_mul_left hdiv
  · have hQ : Nat.card Q = 32 := by
      norm_num at hdimension
      rw [hdimension] at hhalf
      omega
    rw [if_pos hQ]
    norm_num [Fin.prod_univ_succ] at hdiv
    exact (hodd.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hdiv

public theorem frattini_quotient_card_eq_sixteen_of_five_dvd
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32)
    (actor : Subgroup (MulAut Q)) (hodd : Odd (Nat.card actor))
    (hfive : 5 ∣ Nat.card actor) : Nat.card (Q ⧸ frattini Q) = 16 := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  obtain ⟨dimension, hdim, hdimension⟩ :=
    exists_frattini_quotient_dimension_le_four htwo hnoncomm hbound
  have hdiv := hfive.trans (Subgroup.card_dvd_of_injective
    ((Subgroup.quotientAut (frattini Q)).comp actor.subtype)
    (odd_frattini_action_injective htwo actor hodd))
  rw [card_mulAut_elementary_two_pow (Q ⧸ frattini Q) dimension hdimension] at hdiv
  have heq : dimension = 4 := by
    by_contra hnot
    have hsmall : dimension ≤ 3 := by omega
    interval_cases dimension <;> norm_num [Fin.prod_univ_succ] at hdiv
  simpa [heq] using hdimension

public theorem frattini_structure_of_quotient_sixteen
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32) (hquotient : Nat.card (Q ⧸ frattini Q) = 16) :
    Nat.card Q = 32 ∧ Nat.card (frattini Q) = 2 ∧ frattini Q ≤ Subgroup.center Q := by
  have hhalf := frattini_quotient_card_le_half htwo hnoncomm
  rw [hquotient] at hhalf
  have hQ : Nat.card Q = 32 := by omega
  have hcount := (frattini Q).index_mul_card
  change Nat.card (Q ⧸ frattini Q) * Nat.card (frattini Q) = Nat.card Q at hcount
  rw [hquotient, hQ] at hcount
  have hfrattini : Nat.card (frattini Q) = 2 := by omega
  exact ⟨hQ, hfrattini, Subgroup.central_of_normal_card_two (frattini Q) hfrattini⟩

public theorem odd_actor_card_dvd_sharp_of_prime_exclusions
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32)
    (actor : Subgroup (MulAut Q)) (hodd : Odd (Nat.card actor))
    (hfive : ¬ 5 ∣ Nat.card actor) (hseven : ¬ 7 ∣ Nat.card actor) :
    Nat.card actor ∣ (if Nat.card Q = 32 then 9 else 3) := by
  have hdiv := odd_actor_card_dvd_coarse htwo hnoncomm hbound actor hodd
  have hcoprimeFive : Nat.Coprime (Nat.card actor) 5 :=
    ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hfive).symm
  have hcoprimeSeven : Nat.Coprime (Nat.card actor) 7 :=
    ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr hseven).symm
  split_ifs at hdiv ⊢
  · exact (hcoprimeFive.mul_right hcoprimeSeven).dvd_of_dvd_mul_left hdiv
  · exact hcoprimeSeven.dvd_of_dvd_mul_left hdiv

end SmallNonabelianTwoGroup
