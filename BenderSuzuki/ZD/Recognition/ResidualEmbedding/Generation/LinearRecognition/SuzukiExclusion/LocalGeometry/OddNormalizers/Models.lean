module
public import BenderSuzuki.SE.Models
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Suzuki embeddings at the common Borel exponent

For q = 2^(2*m+1), the actual Suzuki order is divisible by five, whereas
PSL₂(q) and PSU₃(q) have orders prime to five. The latter assertion uses
the projective unitary order, including its scalar denominator. Therefore
an injective map from Sz(q) to a simple Bender model with this same
exponent forces the Suzuki alternative and is surjective by cardinality.

This is the precise part of GLS4, Chapter 4, Lemma 3.9(a) needed in
Chapter 2, Lemma 14.2(d). The consumer must identify the common exponent;
a family tag without that identification would not suffice. Sources:
`refs/KGroup/GLS4/Chapter4.tex`, and the actual order formulas in
Huppert II.6.14, II.10.12 and Huppert–Blackburn III.XI.3.3.
-/

namespace BenderSuzuki.ZD.SuzukiExclusion
open _root_.BenderSuzuki.MatrixGroups Subgroup PFAppendixIII

private theorem binary_odd_square_mod_five (m : ℕ) :
    (2 ^ (2 * m + 1)) ^ 2 % 5 = 4 := by
  rw [← pow_mul, show (2 * m + 1) * 2 = 4 * m + 2 by omega, pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

private theorem binary_odd_mod_five (m : ℕ) :
    2 ^ (2 * m + 1) % 5 = 2 ∨ 2 ^ (2 * m + 1) % 5 = 3 := by
  have hs := binary_odd_square_mod_five m
  have ht := Nat.mod_lt (2 ^ (2 * m + 1)) (by decide : 0 < 5)
  interval_cases h : 2 ^ (2 * m + 1) % 5
  all_goals norm_num [Nat.pow_mod, h] at hs
  all_goals decide

public theorem five_dvd_suzuki_card {m : ℕ} (hm : 0 < m) :
    5 ∣ Nat.card (SuzukiMatrixGroup m) := by
  rw [suzukiMatrixGroup_card m hm]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply Nat.dvd_iff_mod_eq_zero.mpr
  rw [Nat.add_mod, binary_odd_square_mod_five]

public theorem five_not_dvd_binary_odd_psl_card (m : ℕ) :
    ¬ 5 ∣ Nat.card (PSL2BinaryMatrixGroup (2 * m + 1)) := by
  let K := BinaryGaloisField (2 * m + 1)
  have hK : Nat.card K = 2 ^ (2 * m + 1) := GaloisField.card 2 _ (by omega)
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq _
  have hc := External.huppert614_card_psl_mul_center (K := K)
  rw [External.huppert614_card_center_of_neg_one_eq_one hneg, hK, mul_one] at hc
  change ¬ 5 ∣ Nat.card (PSL2MatrixGroup K)
  rw [hc]
  intro hd
  have hpos : 1 ≤ (2 ^ (2 * m + 1)) ^ 2 := Nat.one_le_pow _ _ Nat.one_le_two_pow
  have hs := binary_odd_square_mod_five m
  have hsub : ((2 ^ (2 * m + 1)) ^ 2 - 1) % 5 = 3 := by omega
  rcases binary_odd_mod_five m with hmod | hmod <;>
    have he := Nat.mod_eq_zero_of_dvd hd <;>
    norm_num [Nat.mul_mod, hmod, hsub] at he

public theorem five_not_dvd_binary_odd_unitary_card (m : ℕ)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ (2 * m + 1)) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ (2 * m + 1)) :
    ¬ 5 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let q := 2 ^ (2 * m + 1)
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ :=
    External.huppert_II_10_12 J q hcard hfixed hJ
  have hden : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    have hd : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 := by
      rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by
        simpa [mul_comm] using Nat.sq_sub_sq q 1]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
    exact dvd_mul_of_dvd_right hd _
  intro hd
  rw [hc] at hd
  have hn := hd.trans (Nat.div_dvd_of_dvd hden)
  have hpos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ Nat.one_le_two_pow
  have hs : q ^ 2 % 5 = 4 := binary_odd_square_mod_five m
  have hsub : (q ^ 2 - 1) % 5 = 3 := by omega
  rcases binary_odd_mod_five m with hmod | hmod <;>
    have he := Nat.mod_eq_zero_of_dvd hn <;>
    norm_num [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hmod, hsub, q] at he

/-- At the common Borel exponent, an actual Suzuki embedding fills the
recognized simple Bender model. -/
public theorem suzuki_surjective_of_bender_atExponent
    {H : Type*} [Group H] [Finite H] {m : ℕ} (hm : 1 ≤ m)
    (hH : IsSimpleBenderGroupAtExponent (2 * m + 1) H)
    (f : SuzukiMatrixGroup m →* H) (hf : Function.Injective f) : Function.Surjective f := by
  have hd := Subgroup.card_dvd_of_injective f hf
  have h5 := (five_dvd_suzuki_card hm).trans hd
  cases hH with
  | isPSL2 he =>
    obtain ⟨e⟩ := he
    exact (five_not_dvd_binary_odd_psl_card m
      (by rwa [← Nat.card_congr e.toEquiv])).elim
  | isSuzuki he =>
    obtain ⟨k, hk, ⟨e⟩⟩ := he
    have hkm : k = m := by omega
    subst k
    exact (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, Nat.card_congr e.toEquiv |>.symm⟩ |>.surjective
  | isPSU3 he =>
    obtain ⟨E, hE, hfin, J, hJ, hcard, hfixed, ⟨e⟩⟩ := he
    let : Field E := hE
    let : Finite E := hfin
    exact (five_not_dvd_binary_odd_unitary_card m J hJ hcard hfixed
      (by rwa [← Nat.card_congr e.toEquiv])).elim

end BenderSuzuki.ZD.SuzukiExclusion
