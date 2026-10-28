module

public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# The solvable endpoint PSU₃(2)

For any nondegenerate ternary Hermitian form over a field of order four,
with conjugation the square map, the actual projective special unitary
group has order 72. The two-and-three case of Burnside's theorem makes
it solvable. The order formula uses a genuine Hermitian basis change;
no standard-form assumption or group-family label replaces the model.

Sources: Huppert, *Endliche Gruppen I*, II.10.12, and Burnside's two-prime
theorem. This handles the nonsimple endpoint in Aschbacher–Smith E.6.8(1),
printed pp.247–248, as used in E.6.22, printed p.254.
-/

public section
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The genuine projective matrix group PSU₃(2) has order 72. -/
theorem card_projective (hcard : Nat.card F = 2 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 2) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 72 := by
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hcard) (by simpa using hconj)
  simpa using Representation.SU3.BinaryDegree.card_projective J hcard hfixed

/-- The nonsimple endpoint is solvable, for every permitted Hermitian form. -/
theorem projective_isSolvable (hcard : Nat.card F = 2 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 2) :
    Group.IsSolvable (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Nat.finite_of_card_ne_zero (by rw [card_projective J hcard hconj]; decide)
  apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  rw [card_projective J hcard hconj, show 72 = 2 ^ 3 * 3 ^ 2 by decide] at hd
  obtain h | h := hp.dvd_mul.mp hd
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      (hp.dvd_of_dvd_pow h))

end BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo
