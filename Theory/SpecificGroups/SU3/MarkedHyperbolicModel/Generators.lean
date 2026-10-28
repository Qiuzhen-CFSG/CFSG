module

public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.SemilinearReduction
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Marked hyperbolic generators for the odd unitary cyclic core

For p congruent to one modulo four, choose a field unit of order
2^(n+3), where 2^(n+2) is the exact two-part of p-1. The existing
antidiagonal SU₃ torus embeds the hyperbolic diagonal block with its
inverse determinant on the remaining line. Its projective scalar kernel
has exponent three, so the rotation keeps its two-power order.
The actual Weyl matrix swaps the hyperbolic coordinates, and entrywise
Frobenius acts with the two required exponents and fixes that swap.

Source: Alperin–Brauer–Gorenstein II.2 Lemma 1, article p.17;
Aschbacher–Smith A.3.21(b), printed p.55, and E.1.14(7), printed p.214.
The cardinality and full-automorphism Sylow arguments are separate.
This strengthens CyclicCoreSylow.Generators, retaining the field unit and
its half-power; the existing unmarked interface remains unchanged.
-/

public section

open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.MarkedHyperbolicModel
open OddPrimeSylow.NormalizedOuter
variable {F : Type*} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private theorem weyl_square : hermitianWeylPSU J hJ ^ 2 = 1 := by
  apply Subtype.ext
  change (ProjGenLinGroup.mk hermitianWeylGL) ^ 2 = 1
  rw [← map_pow]
  have he : (hermitianWeylGL : GL (Fin 3) F) ^ 2 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  rw [he, map_one]

private theorem weyl_action (k : Fˣ) :
    hermitianWeylPSU J hJ * hermitianTorusPSU J hJ k * (hermitianWeylPSU J hJ)⁻¹ =
      hermitianTorusPSU J hJ ((Units.map J.conj.toMonoidHom k)⁻¹) := by
  have hw : (hermitianWeylPSU J hJ)⁻¹ = hermitianWeylPSU J hJ :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using weyl_square J hJ)
  rw [hw]
  apply Subtype.ext
  change ProjGenLinGroup.mk hermitianWeylGL * ProjGenLinGroup.mk (hermitianTorusGL J k) *
    ProjGenLinGroup.mk hermitianWeylGL =
      ProjGenLinGroup.mk (hermitianTorusGL J ((Units.map J.conj.toMonoidHom k)⁻¹))
  rw [← map_mul, ← map_mul]
  apply congrArg ProjGenLinGroup.mk
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusGL, hermitianTorusMatrix, hermitianWeylGL,
      hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      J.conj_involutive (k : F), mul_comm]

private theorem entrywise_torus (k : Fˣ) :
    entrywiseProjectiveAut J hJ (hermitianTorusPSU J hJ k) =
      hermitianTorusPSU J hJ (Units.map J.conj.toMonoidHom k) := by
  have hp (v : Fˣ) : hermitianTorusPSU J hJ v =
      J.specialToProjective (hermitianTorusSU J hJ v) := by
    apply Subtype.ext
    rw [hermitianTorusPSU_val, specialToProjective_apply_val]
    rfl
  rw [hp, entrywiseProjectiveAut_specialToProjective, hp]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [entrywiseSpecialAut_apply_val]
  change (hermitianTorusMatrix J k).map J.conj =
    hermitianTorusMatrix J (Units.map J.conj.toMonoidHom k)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianTorusMatrix]

private theorem entrywise_weyl : entrywiseProjectiveAut J hJ (hermitianWeylPSU J hJ) =
    hermitianWeylPSU J hJ := by
  have hp : hermitianWeylPSU J hJ = J.specialToProjective (hermitianWeylSU J hJ) := by
    apply Subtype.ext
    rw [hermitianWeylPSU_val, specialToProjective_apply_val]
    rfl
  rw [hp, entrywiseProjectiveAut_specialToProjective]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [entrywiseSpecialAut_apply_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianWeylSU, hermitianWeylGL, hermitianWeylMatrix]

/-- The hyperbolic rotation and swap on the actual projective model, with
both literal entrywise-Frobenius formulas. The projective scalar kernel is cubic. -/
theorem exists_marked_generators [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (n : ℕ) (hdiv : 2 ^ (n + 2) ∣ p - 1) (hodd : Odd ((p - 1) / 2 ^ (n + 2))) :
    ∃ r : Fˣ, orderOf r = 2 ^ (n + 3) ∧
      r ^ (2 ^ (n + 2)) = -1 ∧ J.conj (r : F) = -(r : F) ∧
      let x := hermitianTorusPSU J hJ r
      let y := hermitianWeylPSU J hJ
      orderOf x = 2 ^ (n + 3) ∧ y ^ 2 = 1 ∧
      y * x * y⁻¹ = x ^ (2 ^ (n + 2) - 1) ∧
      entrywiseProjectiveAut J hJ x = x ^ (2 ^ (n + 2) + 1) ∧
      entrywiseProjectiveAut J hJ y = y := by
  have hdivF : 2 ^ (n + 3) ∣ Nat.card F - 1 := by
    rw [hcard, show p ^ 2 - 1 = (p - 1) * (p + 1) by
      simpa only [one_pow, mul_comm] using Nat.sq_sub_sq p 1,
      show n + 3 = (n + 2) + 1 by omega, pow_succ]
    exact Nat.mul_dvd_mul hdiv (even_iff_two_dvd.mp ho.add_one)
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hdu : 2 ^ (n + 3) ∣ orderOf u := by rw [hu, Nat.card_units]; exact hdivF
  let r := u ^ (orderOf u / 2 ^ (n + 3))
  have hr : orderOf r = 2 ^ (n + 3) := orderOf_pow_orderOf_div (orderOf_pos u).ne' hdu
  have hp1 : 1 ≤ p := hp.one_le
  obtain ⟨k, hk⟩ := hodd
  have hrep : p - 1 = 2 ^ (n + 2) * (2 * k + 1) := by
    rw [← hk]; exact (Nat.mul_div_cancel' hdiv).symm
  have hexp : p = 2 ^ (n + 3) * k + (2 ^ (n + 2) + 1) := by
    rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
    nlinarith only [hrep, Nat.sub_add_cancel hp1]
  have hpow : r ^ p = r ^ (2 ^ (n + 2) + 1) := by
    rw [hexp, pow_add, pow_mul, ← hr, pow_orderOf_eq_one, one_pow, one_mul]
  have hhalf : r ^ (2 ^ (n + 2)) = (-1 : Fˣ) := by
    have hs : ((r : F) ^ (2 ^ (n + 2))) ^ 2 = 1 := by
      rw [← pow_mul, show 2 ^ (n + 2) * 2 = 2 ^ (n + 3) by ring]
      exact congrArg Units.val (hr ▸ pow_orderOf_eq_one r)
    have hn : (r : F) ^ (2 ^ (n + 2)) ≠ 1 := by
      intro hh
      have hh' : r ^ (2 ^ (n + 2)) = 1 := Units.ext hh
      exact pow_ne_one_of_lt_orderOf (by positivity)
        (by rw [hr]; exact Nat.pow_lt_pow_right (by decide) (by omega)) hh'
    apply Units.ext
    exact (sq_eq_one_iff.mp hs).resolve_left hn
  have hconj : J.conj (r : F) = -(r : F) := by
    rw [hc]
    have hh : r ^ p = -r := by
      rw [hpow, pow_succ, hhalf, neg_one_mul]
    exact congrArg Units.val hh
  have hinv : (r ^ p)⁻¹ = r ^ (2 ^ (n + 2) - 1) := by
    apply inv_injective
    rw [inv_inv]
    apply eq_inv_of_mul_eq_one_left
    rw [hpow, ← pow_add]
    have he : 2 ^ (n + 2) + 1 + (2 ^ (n + 2) - 1) = 2 ^ (n + 3) := by
      have hpos : 0 < 2 ^ (n + 2) := by positivity
      rw [show 2 ^ (n + 3) = 2 ^ (n + 2) * 2 by ring]
      omega
    rw [he, ← hr, pow_orderOf_eq_one]
  have hγ : Units.map J.conj.toMonoidHom r = r ^ p := by
    apply Units.ext
    exact hc r
  refine ⟨r, hr, hhalf, hconj, ?_, weyl_square J hJ, ?_, ?_, entrywise_weyl J hJ⟩
  · rw [(hermitianTorusPSU J hJ).orderOf_map_eq_of_coprime_of_isPGroup_ker
      (BorelTorus.projective_ker_isThreeGroup J hJ) r (by rw [hr]; exact (by decide : Nat.Coprime 3 2).pow_right _)]
    exact hr
  · rw [weyl_action, hγ, hinv, map_pow]
  · rw [entrywise_torus, hγ, hpow, map_pow]

/-- The quarter-power of the rotation parameter is a fixed square root of -1. -/
theorem fixed_sqrt_neg_one (r : Fˣ) (n : ℕ)
    (hhalf : r ^ (2 ^ (n + 2)) = -1) (hr : J.conj (r : F) = -(r : F)) :
    ∃ i : F, i ^ 2 = -1 ∧ J.conj i = i := by
  refine ⟨(r : F) ^ (2 ^ (n + 1)), ?_, ?_⟩
  · rw [← pow_mul, show 2 ^ (n + 1) * 2 = 2 ^ (n + 2) by ring]
    exact congrArg Units.val hhalf
  · rw [map_pow, hr]
    apply Even.neg_pow
    exact ⟨2 ^ n, by simp [pow_succ, mul_two]⟩

end BenderSuzuki.MatrixGroups.HermitianForm.MarkedHyperbolicModel
