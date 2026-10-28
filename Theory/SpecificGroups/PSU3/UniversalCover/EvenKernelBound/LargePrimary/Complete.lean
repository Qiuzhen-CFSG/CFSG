module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.LargePrimary
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic

/-!
# Excluding all primes above three from even-field PSU₃ kernels

For `q = 2^n` with `n ≥ 2`, every finite perfect central cover of the actual
projective special unitary group has kernel order prime to every prime `r > 3`.
If `r` divides `q + 1`, use the rank-two frame torus and its swapped lifts.
Otherwise the characteristic-independent cross-characteristic theorem combines
the cyclic Sylow arguments for `q - 1` and `q² - q + 1` with transfer for primes
absent from the group order.

Applying this bound to the constructed universal cover gives the literal
`universalProjection` kernel bound required by `OddPartDescent.exists_lift_even`.
The original Hermitian form and Frobenius are retained, including `q = 4` and
`q = 8`; no extra three-primary bound is asserted here.

Source: Aschbacher–Smith I.1.2–I.1.3, printed p.407 (PDF p.418);
GLS3, Theorem 6.1.4 and Tables 6.1.2–3.
-/

public section

open BenderSuzuki.MatrixGroups PerfectCentralCovering

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.LargePrimary

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- No prime above three divides the kernel of a finite perfect central cover
of PSU₃ over an even field with parameter at least four. -/
theorem not_dvd_cover_kernel {n r : ℕ} (hn : 2 ≤ n)
    (hr : r.Prime) (hr3 : 3 < r)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  by_cases hd : r ∣ 2 ^ n + 1
  · exact not_dvd_cover_kernel_of_dvd_add_one J hn hr hr3 hd hcard hconj f
  · exact OddKernelBound.OddCrossCharacteristic.not_dvd_kernel_of_not_dvd_add_one
      (p := 2) (e := n) J Nat.prime_two (by omega) hr
      (by omega) (by omega) (by omega) hcard hconj hd f

/-- The full large-prime bound for the original universal projection; this
supplies `hlarge` in `OddPartDescent.exists_lift_even`. -/
theorem not_dvd_universal_kernel {n r : ℕ} (hn : 2 ≤ n)
    (hr : r.Prime) (hr3 : 3 < r)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ¬ r ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let := projective_isQuasisimple J hq hcard hconj
  exact not_dvd_cover_kernel J hn hr hr3 hcard hconj (universalCover _)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.LargePrimary
