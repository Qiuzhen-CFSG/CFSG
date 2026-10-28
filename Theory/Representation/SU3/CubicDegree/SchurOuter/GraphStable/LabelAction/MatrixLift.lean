module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm
public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Lifting an outer involution to the original special unitary matrices

Transport the genuine projective automorphism to an antidiagonal Hermitian
basis and apply the unitary-semilinear normal form there. Conjugating its
special-unitary lift back gives a matrix formula over the original form:
a fixed invertible matrix followed by the stored field involution.
The lift commutes with the literal special-to-projective projection.

Source: GLS III, 2.5.12 and 2.7; GM04, Proposition 4.11, graph case.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open BenderSuzuki.MatrixGroups Matrix
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

private def unitaryAut (u : J.unitarySubgroup) : MulAut J.specialSubgroup where
  toFun := J.specialUnitaryConj u
  invFun := J.specialUnitaryConj u⁻¹
  left_inv x := by apply Subtype.ext; simp [J.specialUnitaryConj_val, mul_assoc]
  right_inv x := by apply Subtype.ext; simp [J.specialUnitaryConj_val, mul_assoc]
  map_mul' x y := by apply Subtype.ext; simp [J.specialUnitaryConj_val, mul_assoc]

private theorem unitaryAut_val (u : J.unitarySubgroup) (x : J.specialSubgroup) :
    (unitaryAut J u x).val = u.val * x.val * u.val⁻¹ := J.specialUnitaryConj_val u x

private theorem unitaryAut_projective (u : J.unitarySubgroup) (x : J.specialSubgroup) :
    J.specialToProjective (unitaryAut J u x) =
      J.unitaryConj u (J.specialToProjective x) :=
  (J.unitaryConj_specialToProjective u x).symm

private theorem projectiveEquiv_projection (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (x : J.specialSubgroup) :
    projectiveEquiv J C hC (J.specialToProjective x) =
      (standardForm J).specialToProjective (specialEquiv J C hC x) := by
  apply Subtype.ext
  rw [projectiveEquiv_apply, J.specialToProjective_apply_val,
    (standardForm J).specialToProjective_apply_val, specialEquiv_apply]
  simp only [map_mul, map_inv]

/-- An outer involution of the actual PSU image has a compatible lift to SU,
whose matrix formula is conjugate-entrywise on the original Hermitian space. -/
theorem outer_involution_matrix_lift [Finite F]
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (ho : ¬ ∃ x, a = MulAut.conj x) :
    ∃ (β : MulAut J.specialSubgroup) (D : GL (Fin 3) F),
      (∀ g, J.specialToProjective (β g) = a (J.specialToProjective g)) ∧
      (∀ g, (β g).val = D * GeneralLinearGroup.map J.conj.toRingHom g.val * D⁻¹) := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s
    (by omega) hcard hconj
  obtain ⟨C, hC⟩ := exists_standard_basis J (2 ^ s) hcard hf
  let J₀ := standardForm J
  let e := projectiveEquiv J C hC
  let d := specialEquiv J C hC
  let a₀ := MulAut.congr e a
  have ha₀ : a₀ ^ 2 = 1 := by
    change (MulAut.congr e a) ^ 2 = 1
    rw [← map_pow, ha, map_one]
  have ho₀ : ¬ ∃ x, a₀ = MulAut.conj x := by
    exact fun h => ho ((MulAut.congr_inner_iff e a).mp h)
  obtain ⟨u, hu⟩ := J₀.outer_involution_normal_form s hs rfl hcard hf
    (J₀.projectiveGraphAut_isEntrywiseConjugation rfl) a₀ ha₀ ho₀
  let β₀ := unitaryAut J₀ u * J₀.specialGraphAut rfl
  have hp₀ (x : J₀.specialSubgroup) :
      J₀.specialToProjective (β₀ x) = a₀ (J₀.specialToProjective x) := by
    change J₀.specialToProjective (unitaryAut J₀ u (J₀.specialGraphAut rfl x)) = _
    rw [unitaryAut_projective, ← J₀.projectiveGraphAut_specialToProjective rfl, hu]
    rfl
  let β := MulAut.congr d.symm β₀
  let D := C * u.val * GeneralLinearGroup.map J.conj.toRingHom C⁻¹
  refine ⟨β, D, ?_, ?_⟩
  · intro g
    apply e.injective
    rw [projectiveEquiv_projection]
    change J₀.specialToProjective (d (d.symm (β₀ (d g)))) =
      e (a (J.specialToProjective g))
    rw [d.apply_symm_apply, hp₀]
    change e (a (e.symm (J₀.specialToProjective (d g)))) = _
    rw [← projectiveEquiv_projection, e.symm_apply_apply]
  · intro g
    change (d.symm (β₀ (d g))).val = _
    rw [specialEquiv_symm_apply]
    change C * (unitaryAut J₀ u (J₀.specialGraphAut rfl (d g))).val * C⁻¹ = _
    rw [unitaryAut_val]
    have hg : (J₀.specialGraphAut rfl (d g)).val =
        GeneralLinearGroup.map J.conj.toRingHom (C⁻¹ * g.val * C) := by
      apply Units.ext
      rw [J₀.specialGraphAut_apply_val]
      change (d g).val.val.map J.conj = _
      rw [specialEquiv_apply]
      rfl
    rw [hg]
    simp [D, map_mul, map_inv, mul_assoc]

end Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction
