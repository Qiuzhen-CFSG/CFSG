module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.Reduction
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.ScalarKernel
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.GramNormalization
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.LinearCocycle
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.SymmetricForms
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Projective descent for involutory unitary twists

For the standard three-dimensional Hermitian form over a quadratic field of
characteristic two, an involutory unitary twist of entrywise conjugation
satisfies the exact matrix cocycle equation `u * conj(u) = 1`. The proof first
uses the faithful projective conjugation action to obtain a scalar, then
removes that scalar with the unitary equation in characteristic two.

Linear semilinear descent and congruence of nondegenerate symmetric ternary
forms over the fixed field then produce a unitary coboundary. The theorem
`projective_descent` discharges both matrix existence premises of the retained
conditional interface. Its application `unitary_twist_conjugate` gives the
literal automorphism conjugacy needed by the outer-involution assembly.

Source: GLS, Volume 3, Proposition 4.9.2(b2,g), specialized to twisted A₂
in characteristic two; GLS, Volume 4, Chapter 4, Lemma 3.4(a,c).
-/

open BenderSuzuki.MatrixGroups Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private theorem descent_form_fixed
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    J.form.map J.conj = J.form := by
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem descent_char_two [Finite E] (n : ℕ)
    (hE : Nat.card E = (2 ^ n) ^ 2) : CharP E 2 := by
  let := Fintype.ofFinite E
  exact charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    rw [← Nat.card_eq_fintype_card, hE, pow_mul])

private theorem descent_conj_nontrivial (n : ℕ) (hn : 2 ≤ n)
    (hE : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n) :
    ∃ t : E, J.conj t ≠ t := by
  by_contra h
  push Not at h
  let e : E ≃ {z : E // J.conj z = z} :=
    { toFun := fun z => ⟨z, h z⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have heq := Nat.card_congr e
  rw [hE, hfixed] at heq
  have hq : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
  nlinarith

/-- An involutory projective unitary twist is an exact matrix cocycle.
The conclusion accounts for, and removes, the scalar kernel of PGL. -/
public theorem unitary_norm_eq_one_of_twist_sq [Finite E]
    (n : ℕ) (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hE : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u : J.unitarySubgroup)
    (hu : (J.unitaryConj u * γ) ^ 2 = 1) :
    u.val * GeneralLinearGroup.map J.conj.toRingHom u.val = 1 := by
  let := descent_char_two n hE
  apply J.norm_eq_one_of_projective_norm_eq_one (descent_form_fixed J hJ) u
  apply ProjGenLinGroup.mk_eq_one.mpr
  apply J.projective_centralizer_scalar hJ (descent_conj_nontrivial J n hn hE hfixed)
  exact J.projective_norm_commutes_of_twist_sq hγ u hu

/-- Conditional projective descent, with the two matrix existence results
displayed separately. `projective_descent` below discharges both premises. -/
public theorem projective_descent_of_linear_descent_and_symmetric_forms [Finite E]
    (n : ℕ) (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hE : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u : J.unitarySubgroup)
    (hu : (J.unitaryConj u * γ) ^ 2 = 1)
    (hlinear : ∀ A : GL (Fin 3) E,
      A * GeneralLinearGroup.map J.conj.toRingHom A = 1 →
      ∃ P : GL (Fin 3) E, A * GeneralLinearGroup.map J.conj.toRingHom P = P)
    (hsymmetric : ∀ S : Matrix (Fin 3) (Fin 3) E,
      S.transpose = S → S.map J.conj = S → S.det ≠ 0 →
      ∃ C : GL (Fin 3) E, C.val.map J.conj = C.val ∧
        C.val.transpose * S * C.val = J.form) :
    ∃ v : J.unitarySubgroup,
      ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk
        (v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹) := by
  obtain ⟨P, hP⟩ := hlinear u.val (J.unitary_norm_eq_one_of_twist_sq n hn hJ hE hfixed hγ u hu)
  obtain ⟨v, hv⟩ := J.unitary_coboundary_of_gram_normalization
    (descent_form_fixed J hJ) u P hP hsymmetric
  exact ⟨v, congrArg ProjGenLinGroup.mk hv⟩

/-- Every involutory unitary twist of entrywise conjugation over the quadratic
field of order `(2^n)^2`, for `n ≥ 2`, is a projective unitary coboundary.
This supplies the descent premise of the outer-involution assembly without
assuming an automorphism normal form or any additional matrix existence result. -/
public theorem projective_descent [Finite E]
    (n : ℕ) (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hE : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u : J.unitarySubgroup)
    (hu : (J.unitaryConj u * γ) ^ 2 = 1) :
    ∃ v : J.unitarySubgroup,
      ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk
        (v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹) := by
  let := descent_char_two n hE
  exact J.projective_descent_of_linear_descent_and_symmetric_forms
    n hn hJ hE hfixed hγ u hu (J.linear_cocycle_descent n hn hE hfixed)
    (J.fixed_symmetric_ternary_congruence hJ)

/-- The unitary coboundary conjugates the specified entrywise automorphism to
the given involutory twist on the actual projective special unitary image. -/
public theorem unitary_twist_conjugate [Finite E]
    (n : ℕ) (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hE : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u : J.unitarySubgroup)
    (hu : (J.unitaryConj u * γ) ^ 2 = 1) :
    ∃ v : J.unitarySubgroup,
      MulAut.congr (J.unitaryConj v) γ = J.unitaryConj u * γ := by
  obtain ⟨v, hv⟩ := J.projective_descent n hn hJ hE hfixed hγ u hu
  exact ⟨v, J.congr_unitaryConj_of_projective_coboundary hγ u v hv⟩

end BenderSuzuki.MatrixGroups.HermitianForm
