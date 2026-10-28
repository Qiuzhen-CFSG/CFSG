module

public import Theory.SpecificGroups.SU3.OuterSolvable
public import Theory.GroupTheory.CyclicNormalOddQuotient.CyclicImage

/-!
# A cyclic normal subgroup in the outer group of PSU₃

Unitary conjugation has cyclic image in Aut/Inn because its determinant
kernel acts by inner automorphisms. Full unitary-semilinear coverage makes
this image normal. The pairs consisting of an automorphism and one of its
field parameters form a group. Its projection to the cyclic field group
has kernel killed by the outer quotient modulo the diagonal image, so that
quotient is cyclic as well. This avoids assuming a unique field part or a
splitting of the diagonal extension.

Source: GLS3, Theorem 2.5.12(b,c,d,f) and §2.7, and the outer-group inspection
in Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.510.
Coverage remains explicit; the odd-prime coverage is proved in a descendant.
-/

public section
open Theory.GroupTheory
open scoped MatrixGroups

namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Unitary conjugation followed by the actual quotient Aut → Aut/Inn. -/
@[expose] def unitaryOuterHom : J.unitarySubgroup →* MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))).comp
    J.unitaryConjHom

/-- The determinant kernel is special unitary and acts by inner automorphisms. -/
theorem unitaryOuterHom_range_isCyclic [Finite E] : IsCyclic J.unitaryOuterHom.range := by
  apply isCyclic_range_of_ker_le_cyclic
    ((Matrix.GeneralLinearGroup.det : GL (Fin 3) E →* Eˣ).comp J.unitarySubgroup.subtype)
  intro u hu
  let x : J.specialSubgroup := ⟨u.val, u.property, hu⟩
  change QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (J.unitaryConjHom u) = 1
  rw [unitaryConjHom_apply]
  rw [show u = (⟨x.val, x.property.1⟩ : J.unitarySubgroup) from rfl,
    J.unitaryConj_special_is_inner]
  exact (QuotientGroup.eq_one_iff _).2 ⟨J.specialToProjective x, rfl⟩

/-- Arbitrary semilinear conjugation preserves the unitary-conjugation image. -/
theorem unitaryConj_range_normal_of_semilinear_coverage [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcover : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    J.unitaryConjHom.range.Normal := by
  constructor
  rintro _ ⟨u, rfl⟩ a
  obtain ⟨σ, ha⟩ := hcover a
  have hu : J.HasUnitarySemilinearForm (J.unitaryConjHom u) 1 :=
    (HasUnitarySemilinearForm.one_iff J).2 ⟨u, J.unitaryConjHom_apply u⟩
  have h := (ha.mul J hJ hu).mul J hJ (ha.inv J hJ)
  rw [mul_one, mul_inv_cancel] at h
  obtain ⟨v, hv⟩ := (HasUnitarySemilinearForm.one_iff J).1 h
  exact ⟨v, (J.unitaryConjHom_apply v).trans hv.symm⟩

/-- The diagonal image is normal in the full outer group under coverage. -/
theorem unitaryOuterHom_range_normal_of_semilinear_coverage [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcover : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    J.unitaryOuterHom.range.Normal := by
  let := J.unitaryConj_range_normal_of_semilinear_coverage hJ hcover
  rw [unitaryOuterHom, MonoidHom.range_comp]
  infer_instance

/-- Modulo the diagonal image, the outer group is cyclic. The group of
semilinear formulas supplies field parameters without assuming their uniqueness. -/
theorem outer_mod_unitary_isCyclic_of_semilinear_coverage [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcover : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ)
    [J.unitaryOuterHom.range.Normal] :
    IsCyclic (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J) ⧸
      J.unitaryOuterHom.range) := by
  let R : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J) × (E ≃+* E)) :=
    { carrier := {x | J.HasUnitarySemilinearForm x.1 x.2}
      one_mem' := by
        change J.HasUnitarySemilinearForm 1 1
        exact (HasUnitarySemilinearForm.one_iff J).2
          ⟨1, J.unitaryConjHom.map_one.symm.trans (J.unitaryConjHom_apply 1)⟩
      mul_mem' := fun ha hb => ha.mul J hJ hb
      inv_mem' := fun ha => ha.inv J hJ }
  let a : R →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (MonoidHom.fst _ _).comp R.subtype
  let d : R →* (E ≃+* E) := (MonoidHom.snd _ _).comp R.subtype
  have ha : Function.Surjective a := by
    intro b
    obtain ⟨σ, hσ⟩ := hcover b
    exact ⟨⟨(b, σ), hσ⟩, rfl⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  let r := QuotientGroup.mk' J.unitaryOuterHom.range
  let := finiteFieldAut_isCyclic (E := E)
  apply isCyclic_of_surjective_of_ker_le_cyclic d (r.comp (q.comp a))
    ((QuotientGroup.mk'_surjective _).comp ((QuotientGroup.mk'_surjective _).comp ha))
  intro x hx
  have hd : x.val.2 = 1 := hx
  have hform := x.property
  change J.HasUnitarySemilinearForm x.val.1 x.val.2 at hform
  rw [hd] at hform
  obtain ⟨u, hu⟩ := (HasUnitarySemilinearForm.one_iff J).1 hform
  change r (q x.val.1) = 1
  apply (QuotientGroup.eq_one_iff _).2
  refine ⟨u, ?_⟩
  change q (J.unitaryConjHom u) = q x.val.1
  rw [unitaryConjHom_apply, hu]

/-- The actual diagonal subgroup witnesses the required outer-group condition.
Arbitrary-automorphism coverage remains an explicit premise. -/
theorem outer_cyclicNormalOddQuotient_of_semilinear_coverage [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcover : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    HasCyclicNormalOddQuotient (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hcover
  let := J.outer_mod_unitary_isCyclic_of_semilinear_coverage hJ hcover
  exact ⟨J.unitaryOuterHom.range, inferInstance, J.unitaryOuterHom_range_isCyclic,
    fun _ _ _ _ _ => inferInstance⟩

end BenderSuzuki.MatrixGroups.HermitianForm
