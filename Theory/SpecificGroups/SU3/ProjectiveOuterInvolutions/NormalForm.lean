module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Semilinear
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.FieldFaithfulness

/-!
# The outer-involution normal form for projective SU₃

Two structural results supply the normal form: arbitrary automorphisms admit concrete
unitary-semilinear formulas, and the field part of an identity formula is
trivial. Squaring a formula therefore shows that its field part squares to
one. A trivial field part would make the automorphism a unitary conjugation;
its cube is inner, so an involution in that subgroup is already inner. The two
field cardinalities identify the remaining field involution with the stored
Hermitian conjugation.

The final theorem discharges both structural premises using `Coverage` and
`FieldFaithfulness`, on the actual projective special unitary image. The
conditional reduction is retained as a separate interface. Source: GLS,
Volume 3, Theorem 2.5.12(a,c,d,f), and the matrix identification in Section 2.7;
the consumer is GLS, Volume 4, Chapter 4, Lemma 3.4(a,c). Conjugacy of the
resulting twists remains the separate matrix-descent argument.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- Conditional reduction from concrete semilinear coverage and uniqueness of
the field component at the identity. Both structural premises must be proved
before this gives the unconditional outer-involution normal form. -/
public theorem outer_involution_normal_form_of_semilinear
    (n : ℕ) (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ)
    (hfaithful : ∀ σ : E ≃+* E, J.HasUnitarySemilinearForm 1 σ → σ = 1)
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ b, a = MulAut.conj b) :
    ∃ u : J.unitarySubgroup, a = J.unitaryConj u * γ := by
  obtain ⟨σ, hσ⟩ := hcoverage a
  have hσsq : σ ^ 2 = 1 := by
    apply hfaithful
    have h := hσ.mul J hJ hσ
    simpa only [← pow_two, ha] using h
  have hσne : σ ≠ 1 := by
    intro h
    rw [h] at hσ
    obtain ⟨u, rfl⟩ := (HasUnitarySemilinearForm.one_iff J).mp hσ
    exact houter (J.unitaryConj_is_inner_of_sq_eq_one u ha)
  have hσJ := J.field_involution_eq_conj n hn hcard hfixed σ hσsq hσne
  rw [hσJ] at hσ
  exact (HasUnitarySemilinearForm.conj_iff J hγ).mp hσ

/-- Every non-inner involution of the actual binary PSU₃ image is a unitary
twist of the specified entrywise Hermitian conjugation. This supplies the
normal-form premise in the outer-involution conjugacy assembly, with no
additional semilinearity or field-faithfulness hypothesis. -/
public theorem outer_involution_normal_form
    (n : ℕ) (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ b, a = MulAut.conj b) :
    ∃ u : J.unitarySubgroup, a = J.unitaryConj u * γ := by
  exact J.outer_involution_normal_form_of_semilinear n hn hJ hcard hfixed
    (J.semilinear_coverage n hn hJ hcard hfixed)
    (J.semilinear_identity_field_eq_one n hn hJ hcard hfixed) hγ a ha houter

end BenderSuzuki.MatrixGroups.HermitianForm
