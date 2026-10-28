module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus.FixedPoints
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.ThreeTorus.Matrix
public import Theory.NumberTheory.BinaryTorusParity

/-!
# The three-primary bound for binary PSU₃ at odd field exponent

For odd `n`, the parameter `q = 2^n` is two modulo three. The actual
three-primary diagonal torus and coordinate cycle therefore have index
prime to three. The fixed-point calculation in the projective norm-one
torus supplies the remaining bound of three. Transport through an
orthonormal basis preserves the input Hermitian form and its involution.
Central transfer then excludes nine from every finite perfect central
cover, in particular from the literal universal projection for `n ≥ 2`.

The scalar quotient and the full three-power torus exponent are retained;
the argument includes `n = 3`, `q = 8`, and all larger three-valuations.
No local configuration or fixed-point premise remains in the conclusions.

Source: Aschbacher–Smith I.1.3(2), printed p.407 (PDF p.418);
GLS III, Theorem 6.1.4 and Tables 6.1.2–3.
-/

public section

open BenderSuzuki.MatrixGroups PerfectCentralCovering

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary

universe u v
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Nine does not divide the kernel of any finite perfect central cover
at odd binary field exponent. The torus and fixed-point inputs are proved. -/
theorem not_nine_dvd_cover_kernel
    {n : ℕ} (hodd : Odd n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {E : Type v} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 3 ^ 2 ∣ Nat.card f.toMonoidHom.ker := by
  have hmod : 2 ^ n % 3 = 2 := by
    simp only [Nat.BinaryTorusParity.two_pow_mod_three, Nat.odd_iff.mp hodd,
      show ¬ (1 : ℕ) = 0 by decide, if_false]
  exact OddKernelBound.OddCrossCharacteristic.OddThreeMatrix.not_nine_dvd_kernel_of_identity_fixed
    J hcard hconj hmod
    (MatrixTorus.normOneTorus_fixed_card_le
      (OddKernelBound.OddCrossCharacteristic.OddThreeMatrix.identityModel J) rfl) f

/-- The actual universal projection has no factor nine in its kernel,
including at `q = 8`. No additional local or covering premise is assumed. -/
theorem not_nine_dvd_universal_kernel
    {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ¬ 3 ^ 2 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let := projective_isQuasisimple J hq hcard hconj
  exact not_nine_dvd_cover_kernel J hodd hcard hconj (universalCover _)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary
