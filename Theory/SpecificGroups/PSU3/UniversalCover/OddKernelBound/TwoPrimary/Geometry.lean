module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary.GeometryData
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary.Geometry.BlockMap

/-!
# Actual odd-index GU₂ local geometry in PSU₃

For any nondegenerate ternary Hermitian form over a finite quadratic field
of odd characteristic, an orthonormal basis transports the determinant-
corrected GU₂ block subgroup into SU₃. Projectivizing this literal map
produces the local data consumed by `not_two_dvd_kernel_of_unitary_local`.
Its index is odd by involution conjugacy; its kernel is a subgroup of the
odd scalar kernel. No central-cover or multiplier bound is assumed.

The prime-power specialization includes p = 3 and p = 5 and both exponents
one and two. Involution conjugacy uses the actual fixed-field cardinality,
so it does not substitute a composite parameter into a prime-field theorem.

Source: Aschbacher–Smith A.3.21(a), printed p.55 (PDF p.66), and the
odd-unitary applications in I.1.3–4, printed pp.407–408 (PDF pp.418–419);
GLS3, §6.1. This is the local geometry, not the independent GU₂
central-extension calculation or its final multiplier assembly.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.TwoPrimary
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The local witness with its chosen basis and literal projective map retained. -/
def unitaryLocalDataOfBasis (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1)
    (hchar : (2 : F) ≠ 0) (q : ℕ) (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) : UnitaryLocalData J where
  form := identityForm (n := 2) J.conj J.conj_involutive
  gram_eq_one := rfl
  conj_eq := rfl
  subgroup := (Geometry.projectiveBlockMap J C hC).range
  odd_index := Geometry.odd_index_projectiveBlockMap J C hC hchar q hcard hfixed
  map := (Geometry.projectiveBlockMap J C hC).rangeRestrict
  surjective := (Geometry.projectiveBlockMap J C hC).rangeRestrict_surjective
  odd_kernel := Geometry.odd_kernel_projectiveBlockMap J C hC

/-- Arbitrary forms over every finite quadratic field of odd characteristic
have the required GU₂ local map. -/
theorem nonempty_unitaryLocalData_of_fixed_card
    (hchar : (2 : F) ≠ 0) (q : ℕ) (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    Nonempty (UnitaryLocalData J) := by
  obtain ⟨C, hC⟩ := External.huppert_II_10_4_a_orthonormal_basis 3 J q hcard hfixed
  exact ⟨unitaryLocalDataOfBasis J C hC hchar q hcard hfixed⟩

/-- The Frobenius specialization for every odd prime power. -/
theorem nonempty_unitaryLocalData_of_odd_prime_power
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e)) :
    Nonempty (UnitaryLocalData J) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow
    (show Fintype.card F = p ^ (e * 2) by
      simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  exact nonempty_unitaryLocalData_of_fixed_card J
    (CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hodd)
    (p ^ e) hcard (card_fixed J hcard hconj)

/-- The exact prime-or-prime-square input for the odd PSU₃ two-primary
transfer consumer, with no excluded small odd primes. -/
theorem nonempty_unitaryLocalData
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (_he1 : 1 ≤ e) (_he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e)) :
    Nonempty (UnitaryLocalData J) :=
  nonempty_unitaryLocalData_of_odd_prime_power J hp hodd hcard hconj

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.TwoPrimary
