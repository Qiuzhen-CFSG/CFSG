module
public import Theory.SpecificGroups.SL3.RadicalNormalizer
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SL2.BinaryLinearComparison
public import Theory.NumberTheory.BinaryTorusParity

/-!
# A cubic in a binary SL₃ radical normalizer detects the field

In odd field degree a full Sylow normalizer has order prime to three.
Every other radical normalizer is a maximal parabolic. Over a field larger
than two its solvable residual has an SL₂ quotient, hence order divisible
by three. Thus a cubic in a radical normalizer whose solvable residual has
three-prime order forces the field to be binary.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890; C.2.7.
-/

/-!
# Cubic radicals in odd binary fields

Let R be a two-radical in SL₃(2ⁿ), with n odd. If its full normalizer
has order divisible by three but its solvable residual has order prime
to three, then n = 1. For n > 1 the radical normalizer is either a
parabolic or a Sylow normalizer. A parabolic residual maps onto SL₂(2ⁿ),
whose order is divisible by three. A Sylow normalizer has order prime
to three, since 3 does not divide 2ⁿ − 1.

The original-plane application is in Chapter13's Inspection.LinearThreeField.
Source: Aschbacher--Smith 13.3.12, printed pp.889--890; the radical
normalizer and parabolic-residual calculations used in 13.6.18.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.RadicalNormalizer
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem three_dvd_local (P : Subgroup SL(3,F))
    (e : (P ⧸ pCore 2 P) ≃* SL(2,F)) : 3 ∣ Nat.card P := by
  have hd : 3 ∣ Nat.card SL(2,F) := by
    by_contra hn
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    rw [Matrix.SL2.binary_threeRank_eq_one] at hz
    exact Nat.one_ne_zero hz
  rw [←Nat.card_congr e.toEquiv] at hd
  exact hd.trans (card_quotient_dvd_card _)

private theorem residual_coprime_congr {A B : Type*} [Group A] [Finite A] [Group B]
    (e : A ≃* B) (hc : Nat.Coprime 3 (Nat.card (solvableResidual A))) :
    Nat.Coprime 3 (Nat.card (solvableResidual B)) := by
  rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,
    card_map_of_injective e.injective]
  exact hc

/-- The literal radical and its full normalizer force degree one. -/
theorem degree_eq_one_of_cubic_and_residual_coprime
    (R : Subgroup SL(3,F)) (hR : R.IsPRadical 2)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (ho : Odd n)
    (hc : 3 ∣ Nat.card (normalizer (R : Set SL(3,F))))
    (hr : Nat.Coprime 3 (Nat.card (solvableResidual (normalizer (R : Set SL(3,F)))))) :
    n = 1 := by
  by_contra he
  have hn2 : 1 < n := by omega
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  let N := normalizer (R : Set SL(3,F))
  rcases radical_normalizer_parabolic_or_sylow R hR hn2 hF with ⟨b,hb⟩ | ⟨S,hS⟩
  · let a := Matrix.HigherLinear.SubspaceTransport.slConj b
    rcases hb with hp | hp
    · let e : N ≃* pointParabolicSL F :=
        (a.subgroupMap N).trans (MulEquiv.subgroupCongr hp)
      have ht := residual_coprime_congr e hr
      have hd := three_dvd_local (pointLocalSL F) (pointLocalSLCoreQuotientEquiv F)
      rw [←pointParabolicSL_residual F hcard,card_map_of_injective
        (pointParabolicSL F).subtype_injective] at hd
      exact Nat.prime_three.coprime_iff_not_dvd.mp ht hd
    · let e : N ≃* lineParabolicSL F :=
        (a.subgroupMap N).trans (MulEquiv.subgroupCongr hp)
      have ht := residual_coprime_congr e hr
      have hd := three_dvd_local (lineLocalSL F) (lineLocalSLCoreQuotientEquiv F)
      rw [←lineParabolicSL_residual F hcard,card_map_of_injective
        (lineParabolicSL F).subtype_injective] at hd
      exact Nat.prime_three.coprime_iff_not_dvd.mp ht hd
  · rw [←hS] at hc
    change 3 ∣ Nat.card (normalizer (S : Set SL(3,F))) at hc
    rw [Nat.card_congr
      (CartanActions.BorelQuotient.sylowSLNormalizerEquiv F hn hF S).toEquiv,
      DefiningSylow.card_borelSL,hF] at hc
    have ht : Nat.Coprime 3 ((2^n)^3 * (2^n-1)^2) :=
      (((by decide : Nat.Coprime 3 2).pow_right n).pow_right 3).mul_right
        ((Nat.BinaryTorusParity.coprime_three_sub_one ho).pow_right 2)
    exact Nat.prime_three.coprime_iff_not_dvd.mp ht hc

end Matrix.PSL3.LinearThree.RadicalNormalizer
