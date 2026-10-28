module

public import Theory.SpecificGroups.SU3.CyclicNormalOuter.OddCoverage
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions
public import Theory.SpecificGroups.SU3.OddInvolutionNormalization.LinearCocycle
public import Theory.SpecificGroups.SU3.OddInvolutionNormalization.SymmetricSimilarity

/-!+# Outer involutions of PSU₃ over every odd prime

The scalar norm of an involutory unitary twist has both square and cube one,
so it is one even in characteristic three. Matrix descent, symmetric ternary
similarity and a scalar norm correction give a projective unitary coboundary.
Semilinear coverage then normalizes every outer involution to entrywise
conjugation by an actual equivalence, retaining the original conjugation and
allowing an arbitrary initial nondegenerate Hermitian Gram matrix.

This extends the congruence-restricted normalization without modifying it.
Source: GLS3, §§2.5, 2.7 and 4.3; Aschbacher–Smith E.6.18, printed p.252,
and Theorem C, printed p.33. Fixed-group ranks are separate obligations.
-/

public section
open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionNormalization
open OddPrimeSylow.NormalizedOuter
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- Exact matrix descent for an involutory unitary twist, for every odd prime. -/
theorem projective_descent {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u : J.unitarySubgroup)
    (hu : (J.unitaryConj u * γ) ^ 2 = 1) :
    ∃ v : J.unitarySubgroup,
      ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk
        (v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹) := by
  have hform : J.form.map J.conj = J.form := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  have h2 := Coverage.two_ne_zero_of_prime_square hp hp3 hcard
  have hconj : ∃ t : E, J.conj t ≠ t := by
    by_contra hn
    push Not at hn
    let e : E ≃ {x : E // J.conj x = x} :=
      { toFun := fun x => ⟨x, hn x⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he := Nat.card_congr e
    rw [hcard, hfixed] at he
    nlinarith
  have hnorm : u.val * GeneralLinearGroup.map J.conj.toRingHom u.val = 1 := by
    apply Descent.norm_eq_one_of_projective_norm_eq_one J hform u
    apply ProjGenLinGroup.mk_eq_one.mpr
    apply Descent.projective_centralizer_scalar J hJ h2 hconj
    exact Descent.projective_norm_commutes_of_twist_sq J hγ u hu
  obtain ⟨P, hP⟩ := linear_cocycle_descent J hp ho hcard hfixed u.val hnorm
  exact Descent.projective_coboundary_of_gram_similarity J p hcard hfixed hform u P hP
    (fixed_symmetric_ternary_similarity J hp ho hcard hfixed hJ)

/-- Every outer involution of the genuine PSU₃ model over an odd prime becomes
entrywise conjugation on an equivalent antidiagonal model. -/
theorem normalized_outer
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ^ 2 = 1) (houter : ¬ ∃ k, a = MulAut.conj k) :
    ∃ (J₀ : HermitianForm 3 E)
      (e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup J₀),
      J₀.conj = J.conj ∧ J₀.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        J₀.IsEntrywiseConjugation (MulAut.congr e a) := by
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J p hcard hfixed
  let : IsSimpleGroup
      (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)) :=
    e.symm.isSimpleGroup
  exact normalized_outer_of_semilinear_and_descent J hp hcard hfixed
    (fun b _ _ => Coverage.semilinear_coverage_odd
      (FormTransport.standardForm J) rfl hp ho hcard hfixed b)
    (fun u hu => projective_descent
      (FormTransport.standardForm J) hp ho hcard hfixed rfl
      (entrywiseProjectiveAut_isEntrywiseConjugation (FormTransport.standardForm J) rfl)
      u hu) a ha houter

end BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionNormalization
