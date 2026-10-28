module

public import Theory.SpecificGroups.SU3.OuterSolvable
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Mathlib.GroupTheory.PGroup

/-!
# The outer action at unitary parameter four

A unitary determinant has fifth power one when Hermitian conjugation is the
fourth-power map. Thus the fifth power of unitary conjugation is inner.
Its cube is also inner by the scalar correction, so unitary conjugation itself
is inner. Every automorphism of the matrix field of order sixteen has fourth
power one. Consequently a semilinear formula makes the fourth power of the
corresponding group automorphism inner.

The resulting assertion about the full outer group explicitly requires
semilinear coverage. This module proves the calculation after coverage, not
coverage itself. No order or simplicity assertion about PSU₃ is assumed.

Source: GLS3, Theorem 2.5.12 and §2.7; the PSU₃(4) local inspection in
Aschbacher–Smith, E.6.23, printed p.254.
-/

public section

open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- At fixed-field order four, every unitary conjugation is inner on the
actual projective special unitary image. -/
theorem unitaryConj_mem_inner_of_fourth_power_conj
    (hconj : ∀ x : E, J.conj x = x ^ 4) (u : J.unitarySubgroup) :
    J.unitaryConj u ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  have hd : (Matrix.GeneralLinearGroup.det u.val) ^ 5 = 1 := by
    apply Units.ext
    change u.val.val.det ^ 5 = 1
    simpa only [hconj, pow_succ] using J.unitary_det_norm_one u
  let v : J.specialSubgroup := ⟨u.val ^ 5, J.unitarySubgroup.pow_mem u.property 5,
    by
      change Matrix.GeneralLinearGroup.det (u.val ^ 5) = 1
      simpa only [map_pow] using hd⟩
  have hv : (J.unitaryConj u) ^ 5 = MulAut.conj (J.specialToProjective v) := by
    rw [← J.unitaryConjHom_apply, ← map_pow]
    rw [J.unitaryConjHom_apply]
    exact J.unitaryConj_special_is_inner v
  obtain ⟨w, hw⟩ := J.unitaryConj_cube_is_inner u
  have h3 : (q (J.unitaryConj u)) ^ 3 = 1 := by
    rw [← map_pow, hw]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩
  have h5 : (q (J.unitaryConj u)) ^ 5 = 1 := by
    rw [← map_pow, hv]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
  have h6 : (q (J.unitaryConj u)) ^ 6 = 1 := by
    rw [show 6 = 3 * 2 from rfl, pow_mul, h3, one_pow]
  rw [show 6 = 5 + 1 from rfl, pow_succ, h5, one_mul] at h6
  exact (QuotientGroup.eq_one_iff _).mp h6

/-- A concrete semilinear formula over the field of order sixteen has inner
fourth power. The field parameter need not be unique. -/
theorem fourth_power_mem_inner_of_semilinear [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = 4 ^ 2) (hconj : ∀ x : E, J.conj x = x ^ 4)
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} {σ : E ≃+* E}
    (ha : J.HasUnitarySemilinearForm a σ) :
    a ^ 4 ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hc : Nat.card (E ≃+* E) = 4 :=
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hcard
  have hσ : σ ^ 4 = 1 := by
    rw [← hc]
    exact pow_card_eq_one'
  have h2 := ha.mul J hJ ha
  have h4 := h2.mul J hJ h2
  have hf : J.HasUnitarySemilinearForm (a ^ 4) 1 := by
    have hh : J.HasUnitarySemilinearForm ((a ^ 2) ^ 2) ((σ ^ 2) ^ 2) := by
      simpa only [pow_two] using h4
    rw [← pow_mul, ← pow_mul] at hh
    simpa only [show 2 * 2 = 4 from rfl, hσ] using hh
  obtain ⟨u, hu⟩ := (HasUnitarySemilinearForm.one_iff J).mp hf
  rw [hu]
  exact J.unitaryConj_mem_inner_of_fourth_power_conj hconj u

/-- With coverage proved, the actual outer automorphism group of PSU₃(4)
is a two-group of exponent dividing four. -/
theorem outer_isTwoGroup_of_four_semilinear_coverage [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = 4 ^ 2) (hconj : ∀ x : E, J.conj x = x ^ 4)
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    IsPGroup 2 (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) x
  obtain ⟨σ, ha⟩ := hcoverage a
  refine ⟨2, ?_⟩
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr
    (J.fourth_power_mem_inner_of_semilinear hJ hcard hconj ha)

end BenderSuzuki.MatrixGroups.HermitianForm
