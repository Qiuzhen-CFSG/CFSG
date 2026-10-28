module

public import Theory.SpecificGroups.PSU3.UniversalCover.Kernel
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# The canonical covering from the actual special-unitary group

The field has order `q²` and its stored involution is `x ↦ x^q`. Finite-field
transport gives the fixed-field order `q`, allowing the established simplicity
and perfectness proofs to supply quasisimplicity of both matrix carriers for
`q > 2`. Their existing surjection is then a `Covering` with exactly the kernel
computed in `Kernel`. The nonsimple endpoint `q = 2` is excluded from the
quasisimplicity theorems.

Source: Huppert II.10.12–13; Aschbacher–Smith I.1.1, I.1.3(2), I.1.4(2),
printed pp.407–408. This module constructs a covering; it does not assert
its universality.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
universe u
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Finiteness of the actual image follows from the special-unitary surjection. -/
instance projective_finite : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

/-- The prescribed quadratic Frobenius has exactly `q` fixed elements. -/
theorem card_fixed {q : ℕ} (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) :
    Nat.card {x : F // J.conj x = x} = q := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hp : IsPrimePow (q ^ 2) := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card F
  obtain ⟨p, n, hp, hn, he⟩ := (isPrimePow_pow_iff (by decide : 2 ≠ 0)).mp hp
  let : Fact p.Prime := ⟨Nat.prime_iff.mpr hp⟩
  subst q
  exact FiniteField.card_fixed_of_quadratic_frobenius J.conj p n hn hcard hconj

/-- SU₃ is quasisimple for `q > 2`, in the prescribed Frobenius convention. -/
theorem special_isQuasisimple {q : ℕ} (hq : 2 < q) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) : IsQuasisimple J.specialSubgroup :=
  J.special_isQuasisimple_of_fixed_card hq hcard (card_fixed J hcard hconj)

/-- The actual projective image is quasisimple for `q > 2`. -/
theorem projective_isQuasisimple {q : ℕ} (hq : 2 < q) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) :
    IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J) :=
  J.projective_isQuasisimple_of_fixed_card hq hcard (card_fixed J hcard hconj)

section Covering
variable [IsQuasisimple J.specialSubgroup]
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]

/-- The covering is the existing special-to-projective matrix homomorphism. -/
def covering : Covering J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  ⟨J.specialToProjective, J.specialToProjective_surjective⟩

@[simp] theorem covering_toMonoidHom :
    (covering J).toMonoidHom = J.specialToProjective := by rfl

end Covering
end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
