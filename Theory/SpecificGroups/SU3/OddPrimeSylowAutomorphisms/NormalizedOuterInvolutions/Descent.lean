module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.MatrixCocycle
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.GramSimilarity
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.LinearCocycle
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.SymmetricSimilarity

/-!
# Odd-prime projective unitary descent: assembly

An involutory unitary twist satisfies the exact matrix cocycle equation,
including characteristic three. A linear descent basis and a fixed-field
similarity of its symmetric Gram matrix then give a projective unitary
coboundary. The scalar in the similarity is removed by the quadratic norm.

Matrix Hilbert 90 in degree three supplies the descent basis, and finite-field
discriminant classification supplies the similarity. The theorem
`projective_descent` discharges both inputs of the conditional assembly below,
including fixed-field order three. It uses no perfectness, simplicity or
arbitrary-automorphism coverage hypothesis.

Source: GLS3, §§2.7 and 4.3; Aschbacher–Smith F.6.18(10)–(11), pp.309–310.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Conditional odd-prime descent with the two independent existence inputs
displayed. `projective_descent` below supplies both inputs. -/
public theorem projective_descent_of_linear_and_similarity [Finite E]
    {p : ℕ} (hp : p.Prime) (hmod : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hlinear : ∀ A : GL (Fin 3) E,
      A * GeneralLinearGroup.map J.conj.toRingHom A = 1 →
      ∃ P : GL (Fin 3) E, A * GeneralLinearGroup.map J.conj.toRingHom P = P)
    (hsimilarity : ∀ S : Matrix (Fin 3) (Fin 3) E,
      S.transpose = S → S.map J.conj = S → S.det ≠ 0 →
      ∃ (a : E) (C : GL (Fin 3) E), a ≠ 0 ∧ J.conj a = a ∧
        C.val.map J.conj = C.val ∧ C.val.transpose * S * C.val = a • J.form)
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u : J.unitarySubgroup)
    (hu : (J.unitaryConj u * γ) ^ 2 = 1) :
    ∃ v : J.unitarySubgroup,
      ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk
        (v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹) := by
  obtain ⟨P, hP⟩ := hlinear u.val
    (unitary_norm_eq_one_of_twist_sq J hJ hp hmod hcard hfixed hγ u hu)
  apply projective_coboundary_of_gram_similarity J p hcard hfixed _ u P hP hsimilarity
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Every involutory unitary twist of entrywise conjugation on the standard
odd-prime PSU₃ model is a projective unitary coboundary. This includes `p = 3`
and has no descent, scalar-centralizer or form-normalization premise. -/
public theorem projective_descent [Finite E]
    {p : ℕ} (hp : p.Prime) (hmod : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u : J.unitarySubgroup)
    (hu : (J.unitaryConj u * γ) ^ 2 = 1) :
    ∃ v : J.unitarySubgroup,
      ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk
        (v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹) := by
  exact projective_descent_of_linear_and_similarity J hp hmod hcard hfixed hJ
    (linear_cocycle_descent J hp hmod hcard hfixed)
    (fixed_symmetric_ternary_similarity J hp hmod hcard hfixed hJ) hγ u hu

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent
