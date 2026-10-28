module

public import Theory.SpecificGroups.SU3.TernaryPerfectKernels.Roots
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.SpecificGroups.SU3.BinaryG2Comparison

/-!
# Three-free perfect central kernels of the actual PSU₃(3) model

The standard-form root calculation transports through the existing Hermitian
basis equivalence to every field-nine form with cube conjugation. In particular
it applies to the literal `ABG.PSU3 3 1` matrix image. The proved exceptional
comparison then transfers the kernel result to the actual commutator subgroup
of the binary octonion automorphism group. Each transport composes the given
cover homomorphism with the group equivalence and preserves its kernel.

Source: Aschbacher–Smith I.1.3 and B.5.7; the exceptional comparison is the
existing Fong recognition theorem, as documented in `BinaryG2Comparison`.
-/

noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectKernels
open OddPrimeSylow.NormalizedOuter.FormTransport

/-- Every finite perfect central cover of an actual field-nine Hermitian
projective special unitary group has kernel prime to three. -/
public theorem not_three_dvd_kernel
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = 3 ^ 2) (hconj : ∀ x, J.conj x = x ^ 3)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 3 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hfixed : Nat.card {x : F // J.conj x = x} = 3 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 3 1 (by decide) (by simpa only [pow_one] using hcard)
      (by simpa only [pow_one] using hconj)
  obtain ⟨e⟩ := exists_projectiveEquiv J 3 hcard hfixed
  let g : PerfectCentralCovering.Cover E
      (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) := {
    toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
    surjective := e.surjective.comp f.surjective
    isPerfect := f.isPerfect
    ker_le_center := by
      intro x hx
      exact f.ker_le_center (e.injective (hx.trans e.map_one.symm)) }
  have hk : g.toMonoidHom.ker = f.toMonoidHom.ker := by
    ext x
    exact ⟨fun hx => e.injective (hx.trans e.map_one.symm),
      fun hx => (congrArg e hx).trans e.map_one⟩
  rw [← hk]
  exact not_three_dvd_kernel_standard (standardForm J) rfl hcard hfixed g

/-- The intrinsic kernel statement on the literal standard `ABG.PSU3 3 1`
carrier, with the covering group in an arbitrary universe. -/
public theorem not_three_dvd_psu3_kernel
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (ABG.PSU3 3 1 (by decide))) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker :=
  not_three_dvd_kernel (ABG.unitaryForm 3 3 1 (by decide))
    (by simpa using GaloisField.card 3 (2 * 1) (by decide))
    (by intro x; simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]) f

end BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectKernels

namespace Atlas.G2

/-- The actual binary octonion commutator model has three-free kernels in
every finite perfect central cover, by the literal PSU₃(3) comparison. -/
public theorem not_three_dvd_binaryDerived_kernel
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (commutator (Model (ZMod 2)))) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨e⟩ := nonempty_commutator_binary_equiv_psu3
  let g : PerfectCentralCovering.Cover E (ABG.PSU3 3 1 (by decide)) := {
    toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
    surjective := e.surjective.comp f.surjective
    isPerfect := f.isPerfect
    ker_le_center := by
      intro x hx
      exact f.ker_le_center (e.injective (hx.trans e.map_one.symm)) }
  have hk : g.toMonoidHom.ker = f.toMonoidHom.ker := by
    ext x
    exact ⟨fun hx => e.injective (hx.trans e.map_one.symm),
      fun hx => (congrArg e hx).trans e.map_one⟩
  rw [← hk]
  exact HermitianForm.TernaryPerfectKernels.not_three_dvd_psu3_kernel g

end Atlas.G2
