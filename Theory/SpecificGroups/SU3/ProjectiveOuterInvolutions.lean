module

public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent

/-!
# Outer involutions of projective SU₃

The matrix route to GLS, Volume 4, Chapter 4, Lemma 3.4(a,c) has two inputs:
an arbitrary outer involution is a unitary twist of entrywise conjugation, and
an involutory twist satisfies a projective matrix descent equation. The latter
equation supplies the conjugating unitary matrix. The compatibility theorem in
`UnitaryConjugation` proves that its action on the actual projective image has
the required conjugacy formula.

The final theorem discharges both inputs using `NormalForm` and `Descent`,
with matrix-field order `q²`, fixed-field order `q`, and `q = 2^n`, `2 ≤ n`.
Thus every outer involution is conjugate to the specified entrywise action
on the actual projective special unitary image. The conditional assembly
interface is retained separately. Construction of that entrywise action and
identification of its fixed group belong to the independent graph-action
development.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm

variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Conditional assembly from an outer-involution normal form and projective
matrix descent. These are independent mathematical inputs, not a claim that
the source classification has already been proved. -/
public theorem outer_involution_conjugate_of_normal_form_and_descent
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ)
    (hnormal : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      a ^ 2 = 1 → (¬ ∃ b, a = MulAut.conj b) →
      ∃ u : J.unitarySubgroup, a = J.unitaryConj u * γ)
    (hdescent : ∀ u : J.unitarySubgroup, (J.unitaryConj u * γ) ^ 2 = 1 →
      ∃ v : J.unitarySubgroup,
        Matrix.ProjGenLinGroup.mk u.val = Matrix.ProjGenLinGroup.mk
          (v.val * (Matrix.GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ b, a = MulAut.conj b) :
    ∃ c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), MulAut.congr c γ = a := by
  obtain ⟨u, rfl⟩ := hnormal a ha houter
  obtain ⟨v, huv⟩ := hdescent u ha
  exact ⟨J.unitaryConj v, J.congr_unitaryConj_of_projective_coboundary hγ u v huv⟩

/-- Every outer involution of the binary projective SU₃ image is conjugate
to the specified entrywise Hermitian conjugation. Both the arbitrary-
automorphism normal form and the projective descent premise are discharged
from the two field cardinalities. This is the outer-conjugacy assertion of
GLS, Volume 4, Chapter 4, Lemma 3.4(a,c), for this concrete model. -/
public theorem outer_involution_conjugate [Finite E]
    (n : ℕ) (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ b, a = MulAut.conj b) :
    ∃ c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), MulAut.congr c γ = a := by
  exact J.outer_involution_conjugate_of_normal_form_and_descent hγ
    (J.outer_involution_normal_form n hn hJ hcard hfixed hγ)
    (J.projective_descent n hn hJ hcard hfixed hγ) a ha houter

end BenderSuzuki.MatrixGroups.HermitianForm
