module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Cubic
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Order
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.SwappedSylow
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.SplitTorus
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.ThreeTorus
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.ThreeTorus.Matrix
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.CyclicTorus

/-!
# Odd cross-characteristic branches of the PSU₃ perfect-cover bound

The q−1 torus and the cubic-factor Sylow calculation exclude every
nondefining prime other than two and three unless it divides q+1. Primes
absent from the projective group order are also excluded by transfer.
The remaining q+1 branch uses the constructed pair of commuting Sylow
generators exchanged by projective conjugation.

The three-primary bound uses the constructed three-primary projective
torus with a cyclic supplement and fixed subgroup of order at most three.
Its odd exponent allows every three-valuation of q+1, including q=5 and
q=17. An orthonormal basis transports both configurations to the given
Hermitian form.

The endpoints `not_dvd_kernel` and `not_nine_dvd_kernel` discharge the
other-prime and three-primary premises of the odd kernel bound, with no
remaining witness assumptions. The former works for every positive prime
power exponent, and the latter for every q congruent to two modulo three.
The earlier conditional reductions are retained as public interfaces.

Source: Aschbacher–Smith I.1.3(2), I.1.4(2), printed pp.407–408
(PDF pp.418–419); GLS3, Theorem 6.1.4 and Tables 6.1.2–3.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

private theorem cube_add_one (q : ℕ) (hq : 1 ≤ q) :
    q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have h := Nat.sub_add_cancel hq2
  nlinarith [congrArg (fun n : ℕ => (q + 1) * n) h]

/-- A prime absent from the target order is absent from the perfect-cover kernel. -/
theorem not_dvd_kernel_of_not_dvd_order {r : ℕ} (hr : r.Prime)
    (hd : ¬ r ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J))
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact r.Prime := ⟨hr⟩
  apply f.not_dvd_card_kernel_of_square_not_dvd
  exact fun h => hd ((dvd_pow_self r (by decide : 2 ≠ 0)).trans h)

/-- All nondefining primes other than two and three outside q+1 are excluded. -/
theorem not_dvd_kernel_of_not_dvd_add_one {p e r : ℕ} (hp : p.Prime)
    (he : 0 < e) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrp : r ≠ p)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    (hplus : ¬ r ∣ p ^ e + 1) {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  let q := p ^ e
  have hq : 1 < q := one_lt_pow₀ hp.one_lt he.ne'
  by_cases hG : r ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)
  · have hqnot : ¬ r ∣ q := by
      intro h
      exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))
    have hs : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    have hg : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
      apply dvd_mul_of_dvd_right
      rw [hs]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (q + 1)) _
    have hd : r ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
      have hG' : r ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
        simpa only [card_projective J hcard hconj] using hG
      exact hG'.trans (Nat.div_dvd_of_dvd hg)
    rcases hr.dvd_mul.mp hd with hd | hd
    · rcases hr.dvd_mul.mp hd with hd | hd
      · rw [cube_add_one q (by omega)] at hd
        have hc := (hr.dvd_mul.mp hd).resolve_left hplus
        exact not_dvd_kernel_of_dvd_cubic J hq hr hr3 hc hcard f
      · exact (hqnot (hr.dvd_of_dvd_pow hd)).elim
    · rw [hs] at hd
      have hm := (hr.dvd_mul.mp hd).resolve_right hplus
      exact EvenKernelBound.CyclicTorus.not_dvd_cover_kernel_of_dvd_sub_one
        J hq hr hr2 hm hcard hconj f
  · exact not_dvd_kernel_of_not_dvd_order J hr hG f

/-- The remaining q+1 input is a literal swapped Sylow pair, not a kernel bound. -/
theorem not_dvd_kernel_of_split_witness {p e r : ℕ} (hp : p.Prime)
    (he : 0 < e) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrp : r ≠ p)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    (hsplit : r ∣ p ^ e + 1 → Nonempty (SwappedSylow J r))
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  by_cases hd : r ∣ p ^ e + 1
  · obtain ⟨d⟩ := hsplit hd
    exact not_dvd_kernel_of_swapped_sylow J hr hr2 d f
  · exact not_dvd_kernel_of_not_dvd_add_one J hp he hr hr2 hr3 hrp hcard hconj hd f

/-- Squares cannot have residue two modulo three. -/
theorem exponent_eq_one_of_mod_two {p e : ℕ} (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hm : (p ^ e) % 3 = 2) : e = 1 := by
  rcases (show e = 1 ∨ e = 2 by omega) with h | rfl
  · exact h
  · have hpmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hpmod with h | h | h <;> simp [Nat.pow_mod, h] at hm

/-- The order-nine cases and square exclusion reduce the remaining bound to the prime-field torus witness. -/
theorem not_nine_dvd_kernel_of_torus_witness {p e : ℕ} (hp : p.Prime)
    (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J))
    (hhigh : e = 1 → p % 3 = 2 → 9 ∣ p + 1 → Nonempty (ThreeTorus J))
    (hm : (p ^ e) % 3 = 2) : ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  have he := exponent_eq_one_of_mod_two he1 he2 hm
  subst e
  simp only [pow_one] at hcard hconj hm
  by_cases h9 : 9 ∣ p + 1
  · obtain ⟨t⟩ := hhigh rfl hm h9
    exact not_nine_dvd_kernel_of_three_torus J t f
  · exact not_nine_dvd_kernel_of_not_nine_dvd_add_one J hp.one_lt hcard hconj hm h9 f

/-- Every nondefining prime other than two and three is excluded from the
kernel of every finite perfect central cover of the actual PSU₃. This also
includes primes absent from its order. It supplies `hother` in
`OddKernelBound.card_kernel_dvd_gcd_of_primary`. -/
theorem not_dvd_kernel {p e r : ℕ} (hp : p.Prime)
    (he : 0 < e) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrp : r ≠ p)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker :=
  not_dvd_kernel_of_split_witness J hp he hr hr2 hr3 hrp hcard hconj
    (fun hd => SplitTorus.nonempty_swappedSylow J hr hr2 hr3 hd hcard hconj) f

/-- Nine is excluded from every perfect-cover kernel when q ≡ -1 modulo
three, without a bound on the three-valuation of q+1. Taking q = p^e
supplies `hthree` in `OddKernelBound.card_kernel_dvd_gcd_of_primary`. -/
theorem not_nine_dvd_kernel {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (hm : q % 3 = 2) {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 9 ∣ Nat.card f.toMonoidHom.ker :=
  OddThreeMatrix.not_nine_dvd_kernel J hcard hconj hm f

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic
