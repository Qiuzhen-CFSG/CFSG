module

public import Theory.SpecificGroups.SU3.TernaryPerfectKernels
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.GroupTheory.PerfectCentralCoverOddPart

/-!
# Two-primary perfect central kernels of PSU₃(3) and G₂(2)′

The actual projective unitary group has order 6048 = 2⁵·3³·7, through
the proved comparison with the binary octonion commutator group. The local
unitary-root argument already excludes three from every perfect central
kernel. Every other odd Sylow subgroup is cyclic by the order, so transfer
excludes every other odd prime as well. Thus each actual covering kernel
is a two-group, without constructing or computing its two-primary part.

This is the precise odd-cover consequence of Aschbacher–Smith I.1.3 used
in A.3.6, printed pp.43–45. All coefficient fields of order nine and all
nondegenerate Hermitian forms with cube Frobenius conjugation are retained.
-/

public section
open Subgroup PerfectCentralCovering BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover

/-- The order belongs to the actual projective Hermitian matrix image. -/
theorem card_projective {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hcard : Nat.card F = 3 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 3) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 6048 :=
  (Nat.card_congr (J.projectiveEquivBinaryG2Derived hcard hconj).toEquiv).trans
    (Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp))

private theorem square_not_dvd_order (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 6048 := by
  intro hd
  have hpd : p ∣ 6048 := (show p ∣ p ^ 2 by
    simpa only [pow_one] using pow_dvd_pow p (by decide : 1 ≤ 2)).trans hd
  change p ∣ 2 * 2 * 2 * 2 * 2 * 3 * 3 * 3 * 7 at hpd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)] at hpd
  have hp7 : p = 7 := by omega
  subst p
  norm_num at hd

private theorem kernel_isTwoGroup_of_order
    {E S : Type*} [Group E] [Finite E] [Group S] [Finite S]
    (f : PerfectCentralCovering.Cover E S) (hcard : Nat.card S = 6048)
    (hthree : ¬ 3 ∣ Nat.card f.toMonoidHom.ker) :
    IsPGroup 2 f.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra hp2
    by_cases hp3 : p = 3
    · exact hthree (hp3 ▸ hpd)
    · let : Fact p.Prime := ⟨hpp⟩
      exact f.not_dvd_card_kernel_of_square_not_dvd
        (by rw [hcard]; exact square_not_dvd_order p hpp hp2 hp3) hpd
  norm_num [heq]

/-- Every finite perfect central cover of the actual ternary projective
unitary group has a two-group kernel. -/
theorem kernel_isTwoGroup {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hcard : Nat.card F = 3 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 3)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    IsPGroup 2 f.toMonoidHom.ker := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv (commutator (Atlas.G2.Model (ZMod 2)))
      (J.projectiveEquivBinaryG2Derived hcard hconj).symm.toEquiv
  exact kernel_isTwoGroup_of_order f (card_projective J hcard hconj)
    (TernaryPerfectKernels.not_three_dvd_kernel J hcard hconj f)

/-- The same assertion for the actual commutator carrier G₂(2)′, using
the proved binary/unitary comparison in the three-primary exclusion. -/
theorem binaryDerived_kernel_isTwoGroup
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (commutator (Atlas.G2.Model (ZMod 2)))) :
    IsPGroup 2 f.toMonoidHom.ker :=
  kernel_isTwoGroup_of_order f
    (Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp))
    (Atlas.G2.not_three_dvd_binaryDerived_kernel f)

end BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover
