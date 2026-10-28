module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.CyclicTorus
public import Theory.SpecificGroups.SU3.OddThreeLocal.CyclicSylow
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.CoveringKernelCard
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime divisors of the characteristic-two PSU₃ universal kernel

The canonical SU₃ projection is a quotient of the universal perfect central
cover. Its scalar-kernel order therefore divides the universal-kernel order.
For `q ≡ 1 (mod 3)`, the actual PSU₃ Sylow three-subgroups are cyclic, including
for arbitrary nondegenerate Hermitian forms. Central transfer excludes three
from every finite perfect central kernel. Thus for `q = 2^n`, `n ≥ 2`, three
divides the universal-kernel order exactly when `n` is odd. The imported cyclic
torus calculation also excludes every odd prime dividing `q-1`.

The final upper bound is conditional on three remaining calculations: exclusion
of two, exclusion of primes other than two and three, and exclusion of nine for
odd `n`. The arithmetic assembly below consumes precisely these bounds; it does
not claim to establish them or the full multiplier theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.1.1–I.1.3,
printed p.407 (PDF p.418); GLS3, Theorem 6.1.4 and Tables 6.1.2–3. The cyclic
Sylow calculation uses Huppert II.10.12 and an actual change of Hermitian form.
-/

public section

open BenderSuzuki.MatrixGroups PerfectCentralCovering

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover

universe u v
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The actual scalar kernel is a quotient of the entire universal kernel.
This is a lower divisibility bound, not a multiplier upper bound. -/
theorem gcd_dvd_universal_kernel_card {q : ℕ} (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    Nat.gcd 3 (q + 1) ∣
      Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  let := special_isQuasisimple J hq hcard hconj
  let := projective_isQuasisimple J hq hcard hconj
  obtain ⟨a, ha, _⟩ := universalProjection_existsUnique_lift
    J.specialToProjective J.specialToProjective_surjective J.specialToProjective_ker_le_center
  have hs : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect J.specialToProjective a
      (ha ▸ universalProjection_surjective _) J.specialToProjective_ker_le_center
  rw [← card_kernel J hcard hconj]
  exact Theory.GroupTheory.kernel_card_dvd_of_surjective_factor _ _ a hs ha

namespace EvenKernelBound

private theorem pow_mod_three_of_even {n : ℕ} (he : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := he
  rw [← two_mul, pow_mul]
  simp [Nat.pow_mod]

private theorem pow_mod_three_of_odd {n : ℕ} (ho : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := ho
  rw [pow_succ, pow_mul]
  simp [Nat.mul_mod, Nat.pow_mod]

/-- Central transfer excludes three from any finite perfect central cover when
the fixed-field order is one modulo three. No standard Gram matrix is assumed. -/
theorem not_three_dvd_cover_kernel_of_mod_one
    {q : ℕ} (hq : 1 < q) (hmod : q % 3 = 1)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    {E : Type v} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  exact f.not_dvd_card_multiplier_of_isCyclic_sylow
    (OddThreeLocal.cyclic_three_sylow_of_mod_one J q hq hmod hcard
      (card_fixed J hcard hconj))

/-- The literal universal kernel has no three-part for even field exponent. -/
theorem not_three_dvd_universal_kernel_of_even
    {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ¬ 3 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let := projective_isQuasisimple J hq hcard hconj
  exact not_three_dvd_cover_kernel_of_mod_one J (by omega) (pow_mod_three_of_even he)
    hcard hconj (universalCover _)

/-- Three occurs in the universal kernel exactly at odd field exponent.
This does not yet bound the exponent of its three-primary part. -/
theorem three_dvd_universal_kernel_iff_odd
    {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    3 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker ↔ Odd n := by
  constructor
  · intro hd
    rcases Nat.even_or_odd n with he | ho
    · exact (not_three_dvd_universal_kernel_of_even J hn he hcard hconj hd).elim
    · exact ho
  · intro ho
    have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) hn)
    have hd : 3 ∣ 2 ^ n + 1 := Nat.dvd_of_mod_eq_zero (by
      have hm := pow_mod_three_of_odd ho
      omega)
    exact (Nat.dvd_gcd (dvd_refl 3) hd).trans
      (gcd_dvd_universal_kernel_card J hq hcard hconj)

private theorem dvd_gcd_of_prime_exclusions {m q : ℕ}
    (htwo : ¬ 2 ∣ m)
    (hlarge : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ∣ m)
    (hnine : ¬ 3 ^ 2 ∣ m)
    (hthree : ¬ 3 ∣ q + 1 → ¬ 3 ∣ m) : m ∣ Nat.gcd 3 (q + 1) := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hpk
  by_cases hk : k = 0
  · simp [hk]
  have hd : p ∣ m := (dvd_pow_self p hk).trans hpk
  by_cases hp2 : p = 2
  · exact (htwo (hp2 ▸ hd)).elim
  by_cases hp3 : p = 3
  · subst p
    have hk2 : k < 2 := by
      by_contra! hh
      exact hnine ((Nat.pow_dvd_pow 3 hh).trans hpk)
    have hk1 : k = 1 := by omega
    rw [hk1, pow_one]
    exact Nat.dvd_gcd (dvd_refl 3) (by
      by_contra hh
      exact hthree hh hd)
  · exact (hlarge p hp hp2 hp3 hd).elim

/-- Assemble the full kernel order from the independent remaining primary
bounds. All three displayed bounds remain genuine proof obligations. -/
theorem card_universal_kernel_eq_of_primary_bounds
    {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (htwo : ¬ 2 ∣ Nat.card
      (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hlarge : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ∣ Nat.card
      (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hnine : Odd n → ¬ 3 ^ 2 ∣ Nat.card
      (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker) :
    Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker =
      Nat.gcd 3 (2 ^ n + 1) := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  apply Nat.dvd_antisymm _ (gcd_dvd_universal_kernel_card J hq hcard hconj)
  apply dvd_gcd_of_prime_exclusions htwo hlarge
  · rcases Nat.even_or_odd n with he | ho
    · intro hd
      exact not_three_dvd_universal_kernel_of_even J hn he hcard hconj
        ((by decide : 3 ∣ 3 ^ 2).trans hd)
    · exact hnine ho
  · intro hnot hd
    have ho := (three_dvd_universal_kernel_iff_odd J hn hcard hconj).mp hd
    exact hnot (Nat.dvd_of_mod_eq_zero (by
      have hm := pow_mod_three_of_odd ho
      omega))

/-- The requested numerical upper bound follows once the three primary
calculations have been discharged. -/
theorem card_universal_kernel_le_of_primary_bounds
    {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (htwo : ¬ 2 ∣ Nat.card
      (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hlarge : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ∣ Nat.card
      (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hnine : Odd n → ¬ 3 ^ 2 ∣ Nat.card
      (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker) :
    Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker ≤
      Nat.gcd 3 (2 ^ n + 1) :=
  (card_universal_kernel_eq_of_primary_bounds J hn hcard hconj htwo hlarge hnine).le

end EvenKernelBound
end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
