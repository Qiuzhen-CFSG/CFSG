module

public import Theory.SpecificGroups.SU3.FourActorInvolutionConjugacy
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model

/-!
# Involution conjugacy for arbitrary ternary Hermitian forms

An orthonormal basis identifies the actual projective matrix group with
its identity-Gram-matrix model. The existing SU₃ involution theorem and
odd scalar-kernel lifting conjugate the two involutions in that model.
Transporting the conjugator back gives conjugacy in the original PSU₃.

This is the form-independent version of the involution calculation in
Aschbacher–Smith A.3.21(a), printed p.55, used for the inner conjugate bound
in K.2, printed p.453. The basis theorem is Huppert II.10.4.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Inner
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

/-- Involution conjugacy for every stored Hermitian Gram matrix, using an
orthonormal basis and the actual special-to-projective quotient. -/
theorem projective_involutions_isConj {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (a b : ProjectiveSpecialUnitaryMatrixGroup J)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨C, hC⟩ := J.exists_orthonormal_basis_of_prime_frobenius hc hcard
  let e := projectiveBasisEquiv J C hC
  have h := Matrix.SU3.projective_involutions_isConj hp2 hcard
    (identityForm J.conj J.conj_involutive) rfl hc (e a) (e b)
    ((e.orderOf_eq a).trans ha) ((e.orderOf_eq b).trans hb)
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, e.symm_apply_apply] using e.symm.toMonoidHom.map_isConj h

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Inner
