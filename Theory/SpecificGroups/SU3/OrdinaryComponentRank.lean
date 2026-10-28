module
public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks

/-!
# Odd-prime rank in binary projective unitary groups

A prime divisor of q+1 supplies the two independent norm-one torus
coordinates in SU₃(q). Away from three the scalar kernel is coprime;
at three the actual projective diagonal/cycle witness supplies rank two.
Thus every PSU₃(2ⁿ), n ≥ 2, has odd-prime rank at least two, retaining
the caller's Hermitian form and Frobenius action.
Source: Aschbacher--Smith A.2.18, and the component-normality argument
used in 15.1.21, printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OrdinaryBorel
variable {F : Type*} [Field F] [Finite F]
/-- The actual projective unitary model has an odd-prime rank-two witness. -/
theorem exists_odd_rank_two (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n)) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ 2 ≤ primeRank r (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨r,hr,hd⟩ := Nat.exists_prime_and_dvd (show 2^n+1 ≠ 1 by have := Nat.two_pow_pos n; omega)
  let : Fact r.Prime := ⟨hr⟩
  have hodd : Odd (2^n+1) := Even.add_odd (Even.pow_of_ne_zero (by decide) (by omega)) (by decide)
  have ho : Odd r := hodd.of_dvd_nat hd
  refine ⟨r,hr,ho,?_⟩
  by_cases h3 : r=3
  · subst r
    exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective J (by omega)
      hcard hconj (by
        have hm := Nat.BinaryTorusParity.two_pow_mod_three n
        have hd' := Nat.mod_eq_zero_of_dvd hd
        rw [Nat.odd_iff]
        split_ifs at hm <;> omega)
  have hk : IsPGroup 3 J.specialToProjective.ker :=
    fun x => ⟨1, by simpa only [pow_one] using J.specialToProjective_ker_cube x⟩
  obtain ⟨a,ha⟩ := hk.exists_card_eq
  have hc : Nat.Coprime r (Nat.card J.specialToProjective.ker) := by
    rw [ha]
    exact (hr.coprime_iff_not_dvd.mpr (fun h => h3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h))).pow_right a
  rw [← primeRank_eq_of_surjective_of_coprime r J.specialToProjective J.specialToProjective_surjective hc]
  exact Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.binary_unitary_special_primeRank_ge_two
    J (by omega) hr hd hcard hconj
end BenderSuzuki.MatrixGroups.HermitianForm.OrdinaryBorel
