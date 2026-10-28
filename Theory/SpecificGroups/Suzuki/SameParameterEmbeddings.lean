module

public import BenderSuzuki.MatrixGroups.PSL2
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder

/-!
# The same-parameter embedding exclusions in Lemma 12.3

For `q = 2^(2m+1)`, the Suzuki order is divisible by `q²+1`, which is
coprime to both the PSL₂ order and the unitary order numerator. Its order
is also prime to three, whereas PSL₂(q) contains a subgroup of order three.
The actual SU₃ projection has kernel of order dividing three, so the same
order argument excludes embeddings into either unitary cover.

These are precisely the exclusions used from GLS4, Chapter 4, Lemma 3.9(a).
The unitary parameter is the fixed-field order, with matrix-field order `q²`.
-/

noncomputable section
namespace BenderSuzuki.MatrixGroups
open Subgroup PFAppendixIII

private theorem psl_card (n : ℕ) (hn : n ≠ 0) :
    Nat.card (PSL2BinaryMatrixGroup n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  let K := BinaryGaloisField n
  have hKcard : Nat.card K = 2 ^ n := by
    simpa [K, BinaryGaloisField] using GaloisField.card 2 n hn
  have hneg : (-1 : K) = 1 := by
    apply (neg_eq_iff_add_eq_zero).2
    have hone : (1 : K) + 1 = 0 := by
      rw [show (1 : K) + 1 = 2 by norm_num]
      exact CharP.cast_eq_zero K 2
    exact hone
  have hcenter := External.huppert614_card_center_of_neg_one_eq_one hneg
  have hpsl := External.huppert614_card_psl_mul_center (K := K)
  rw [hcenter, hKcard] at hpsl
  simpa [K] using hpsl

private theorem cyclotomic_coprime (q : ℕ) (hq : 2 ≤ q) (heven : Even q) :
    Nat.Coprime (q ^ 2 + 1) q ∧ Nat.Coprime (q ^ 2 + 1) (q ^ 2 - 1) ∧
      Nat.Coprime (q ^ 2 + 1) (q ^ 3 + 1) := by
  have hc2 : Nat.Coprime (q ^ 2 + 1) (q ^ 2) := by
    rw [Nat.add_comm (q ^ 2) 1]
    exact (Nat.coprime_add_self_left (m := 1) (n := q ^ 2)).2
      (Nat.coprime_one_left (q ^ 2))
  have hcq := hc2.coprime_dvd_right (dvd_pow_self q (by norm_num : 2 ≠ 0))
  have hpos : 0 < q ^ 2 := by positivity
  have hodd : Odd (q ^ 2 - 1) := Nat.Even.sub_odd hpos
    (Nat.even_pow.mpr ⟨heven, by norm_num⟩) odd_one
  have hcs : Nat.Coprime (q ^ 2 + 1) (q ^ 2 - 1) := by
    have hc := (Nat.coprime_self_add_right (m := q ^ 2 - 1) (n := 2)).2
      hodd.coprime_two_right
    have hp : 0 < q ^ 2 := by positivity
    have he : q ^ 2 - 1 + 2 = q ^ 2 + 1 := by omega
    rw [he] at hc
    exact hc.symm
  have hcminus : Nat.Coprime (q ^ 2 + 1) (q - 1) := hcs.coprime_dvd_right
    (by simpa using Nat.sub_dvd_pow_sub_pow q 1 2)
  refine ⟨hcq, hcs, ?_⟩
  have he : q * (q ^ 2 + 1) - (q ^ 3 + 1) = q - 1 := by
    have hmul : q * (q ^ 2 + 1) = q ^ 3 + q := by ring
    rw [hmul]
    omega
  have hd : Nat.gcd (q ^ 2 + 1) (q ^ 3 + 1) ∣ q - 1 := by
    rw [← he]
    exact Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) q)
      (Nat.gcd_dvd_right _ _)
  exact Nat.eq_one_of_dvd_coprimes hcminus (Nat.gcd_dvd_left _ _) hd

/-- Suzuki at the same field size does not embed into PSL₂. -/
public theorem suzuki_not_injective_psl (m : ℕ) (hm : 1 ≤ m)
    (f : SuzukiMatrixGroup m →* PSL2BinaryMatrixGroup (2 * m + 1)) :
    ¬ Function.Injective f := by
  intro hf
  let q := 2 ^ (2 * m + 1)
  have hq : 2 ≤ q := Nat.le_pow (by omega : 0 < 2 * m + 1)
  have hc := cyclotomic_coprime q hq (even_two.pow_of_ne_zero (by omega))
  have hd : q ^ 2 + 1 ∣ Nat.card (SuzukiMatrixGroup m) := by
    rw [suzukiMatrixGroup_card m (by omega)]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hd' := hd.trans (card_dvd_of_injective f hf)
  rw [psl_card _ (by omega)] at hd'
  have he := Nat.eq_one_of_dvd_coprimes (hc.1.mul_right hc.2.1) (dvd_refl _) hd'
  have hp : 0 < q ^ 2 := by positivity
  omega

/-- PSL₂ at a Suzuki field size cannot embed in the three-free Suzuki group. -/
public theorem psl_not_injective_suzuki (m : ℕ) (hm : 1 ≤ m)
    (f : PSL2BinaryMatrixGroup (2 * m + 1) →* SuzukiMatrixGroup m) :
    ¬ Function.Injective f := by
  intro hf
  have hfour : 4 ^ m % 3 = 1 := by
    change Nat.ModEq 3 (4 ^ m) 1
    simpa only [one_pow] using (show Nat.ModEq 3 4 1 by norm_num [Nat.ModEq]).pow m
  have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul]
    norm_num only [Nat.reducePow] at *
    rw [Nat.mul_mod, hfour]
  have hsq : (2 ^ (2 * m + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have hd : 3 ∣ Nat.card (PSL2BinaryMatrixGroup (2 * m + 1)) := by
    rw [psl_card _ (by omega)]
    apply dvd_mul_of_dvd_right
    · apply Nat.dvd_iff_mod_eq_zero.mpr
      omega
  exact suzukiMatrixGroup_three_free m (by omega) (hd.trans (card_dvd_of_injective f hf))

private theorem projective_card_dvd {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {q : ℕ} (_hq : 2 ≤ q)
    (hcard : Nat.card E = q ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
  rw [Representation.SU3.BinaryDegree.card_projective J hcard hfixed]
  apply Nat.div_dvd_of_dvd
  apply dvd_mul_of_dvd_right
  have he : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [Nat.sub_mul, one_mul]
    have hmul : q * (q + 1) = q ^ 2 + q := by ring
    rw [hmul]
    omega
  rw [he]
  exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (q + 1)) _

private theorem special_card_dvd {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {q : ℕ} (hq : 2 ≤ q)
    (hcard : Nat.card E = q ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Nat.card J.specialSubgroup ∣ ((q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1)) * 3 := by
  have he := QuotientGroup.quotientKerEquivOfSurjective
    J.specialToProjective J.specialToProjective_surjective
  rw [card_eq_card_quotient_mul_card_subgroup J.specialToProjective.ker,
    Nat.card_congr he.toEquiv]
  exact Nat.mul_dvd_mul (projective_card_dvd J hq hcard hfixed)
    J.card_specialToProjective_ker_dvd_three

/-- The Suzuki cyclotomic factor excludes the projective unitary target. -/
public theorem suzuki_not_injective_projective_unitary
    (m : ℕ) (hm : 1 ≤ m) {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E)
    (hcard : Nat.card E = (2 ^ (2 * m + 1)) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ (2 * m + 1))
    (f : SuzukiMatrixGroup m →* ProjectiveSpecialUnitaryMatrixGroup J) :
    ¬ Function.Injective f := by
  intro hf
  let q := 2 ^ (2 * m + 1)
  have hq : 2 ≤ q := Nat.le_pow (by omega : 0 < 2 * m + 1)
  have hc := cyclotomic_coprime q hq (even_two.pow_of_ne_zero (by omega))
  have hd : q ^ 2 + 1 ∣ Nat.card (SuzukiMatrixGroup m) := by
    rw [suzukiMatrixGroup_card m (by omega)]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hd' := hd.trans ((card_dvd_of_injective f hf).trans (projective_card_dvd J hq hcard hfixed))
  have he := Nat.eq_one_of_dvd_coprimes ((hc.2.2.mul_right (hc.1.pow_right 3)).mul_right hc.2.1)
    (dvd_refl _) hd'
  have hp : 0 < q ^ 2 := by positivity
  omega

/-- The same exclusion retains the actual special unitary cover and its
possible central kernel of order three. -/
public theorem suzuki_not_injective_special_unitary
    (m : ℕ) (hm : 1 ≤ m) {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E)
    (hcard : Nat.card E = (2 ^ (2 * m + 1)) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ (2 * m + 1))
    (f : SuzukiMatrixGroup m →* J.specialSubgroup) :
    ¬ Function.Injective f := by
  intro hf
  let q := 2 ^ (2 * m + 1)
  have hq : 2 ≤ q := Nat.le_pow (by omega : 0 < 2 * m + 1)
  have hc := cyclotomic_coprime q hq (even_two.pow_of_ne_zero (by omega))
  have hd : q ^ 2 + 1 ∣ Nat.card (SuzukiMatrixGroup m) := by
    rw [suzukiMatrixGroup_card m (by omega)]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hc3 : Nat.Coprime (q ^ 2 + 1) 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr
    (fun h3 => suzukiMatrixGroup_three_free m (by omega) (h3.trans hd))).symm
  have hd' := hd.trans ((card_dvd_of_injective f hf).trans (special_card_dvd J hq hcard hfixed))
  have he := Nat.eq_one_of_dvd_coprimes
    (((hc.2.2.mul_right (hc.1.pow_right 3)).mul_right hc.2.1).mul_right hc3) (dvd_refl _) hd'
  have hp : 0 < q ^ 2 := by positivity
  omega

end BenderSuzuki.MatrixGroups
