module

public import Theory.Representation.SU3.BinaryDegree.CentralCover
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.Representation.SU3.BinaryDegree.Perfectness
public import Theory.NumberTheory.BinaryPrimitiveDivisor.SixMultiple
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The binary degree minimum for SU₃

For `q = 2^n > 2`, PSU₃(q) is simple. A prime whose binary multiplicative
order is `6*n` divides its order. Since SU₃(q) is perfect, every nontrivial
binary action has kernel contained in the scalar kernel, so its faithful
action quotient still covers PSU₃(q). The binary general linear group
order formula then forces dimension at least `6*n`.

This argument applies to all nontrivial actions, including irreducibles
factoring through PSU₃. It retains arbitrary Hermitian forms by actual
basis-change equivalences. It needs neither a classification of irreducibles
nor an assumption that the natural representation realizes the minimum.

The theorem `finrank_ge` discharges the perfectness and primitive-prime
premises of `finrank_ge_of_perfect_of_primitive_prime` using the concrete
matrix commutator calculation and cyclotomic argument in the imported
modules. The specialization `finrank_ge_of_irreducible` gives the form used
by the quasithin consumer, retaining the essential nontriviality hypothesis.

Sources: Aschbacher--Smith, *The Classification of Quasithin Groups*, printed
p.356 and A.3.6(2), printed p.43. This is an alternative to the twisted
Frobenius-orbit argument in GLS3 §2.8; the needed primitive-divisor theorem
is GLS2, Chapter A, Theorem 1.1, with exponent `6*n ≥ 12`.
-/

public section

open BenderSuzuki.MatrixGroups

namespace Representation.SU3.BinaryDegree

/-- The unitary degree bound from perfectness and one primitive binary prime.
Neither faithfulness nor irreducibility is required of the representation. -/
theorem finrank_ge_of_perfect_of_primitive_prime
    {F V : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hperfect : Group.IsPerfect J.specialSubgroup)
    (hprime : ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = 6 * n)
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) J.specialSubgroup V)
    (hρ : ∃ g, ρ g ≠ 1) : 6 * n ≤ Module.finrank (ZMod 2) V := by
  let : Group.IsPerfect J.specialSubgroup := hperfect
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have hq : 2 < 2 ^ n := (by decide : 2 < 2 ^ 2).trans_le
    (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J (2 ^ n) hq hcard hf
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨p, hp, ho⟩ := hprime
  rw [← ho]
  exact orderOf_le_finrank_of_perfect_central_cover
    J.specialToProjective J.specialToProjective_surjective
    J.specialToProjective_ker_le_center ρ hρ hp
    (prime_ne_two_of_order (by omega) ho)
    (prime_dvd_card_projective J (by omega) hcard hconj hp ho)

/-- Every nontrivial binary representation of SU₃(2ⁿ), for `n ≥ 2`, has
dimension at least `6*n`. This includes actions through PSU₃ and arbitrary
nondegenerate Hermitian forms. -/
theorem finrank_ge
    {F V : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) J.specialSubgroup V)
    (hρ : ∃ g, ρ g ≠ 1) : 6 * n ≤ Module.finrank (ZMod 2) V :=
  finrank_ge_of_perfect_of_primitive_prime J hn hcard hconj
    (isPerfect_specialSubgroup J hn hcard hconj)
    (Theory.NumberTheory.exists_prime_orderOf_two_six_mul hn) ρ hρ

/-- The universal nontrivial irreducible SU₃ binary degree bound used on
printed p.356 of Aschbacher--Smith. Faithfulness is not required, so this
applies to both special and projective actions in A.3.6. -/
theorem finrank_ge_of_irreducible
    {F V : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) J.specialSubgroup V)
    (_hirr : ρ.IsIrreducible) (hρ : ∃ g, ρ g ≠ 1) :
    6 * n ≤ Module.finrank (ZMod 2) V :=
  finrank_ge J hn hcard hconj ρ hρ

end Representation.SU3.BinaryDegree
