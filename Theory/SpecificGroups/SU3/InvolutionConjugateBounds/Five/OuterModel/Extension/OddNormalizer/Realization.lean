module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Extension.OddNormalizer.Matrices
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Embedding.Relations
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Extension.Intertwiner

/-!
# The odd action on the projective alternating subgroup

The existing five special-unitary Suzuki lifts define the actual projective
A₇ embedding. We record their images after the explicit Hermitian basis change.
The checked Frobenius intertwiner inverts those five generators, exactly as
conjugation by the transposition `(0 1)` does. Equality on the Suzuki generators
therefore gives equality on all of A₇. All maps descend through the actual PGL
image; the tail lifts need not be linear involutions.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11. The matrix construction and relations are reused from
`InnerModel.Embedding`; this module adds their odd intertwining action.
-/

@[expose] public noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer.OddNormalizer
open Matrix Equiv GLS3.Chapter5.SchurPresentation
open BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
open OddPrimeSylow.NormalizedOuter

def fieldActor : MulAut (ProjectiveSpecialUnitaryMatrixGroup fieldForm) :=
  entrywiseProjectiveAut fieldForm rfl

def fieldTwist : MulAut (ProjectiveSpecialUnitaryMatrixGroup fieldForm) :=
  fieldForm.unitaryConj intertwiner * fieldActor

theorem fieldActor_entrywise : fieldForm.IsEntrywiseConjugation fieldActor :=
  entrywiseProjectiveAut_isEntrywiseConjugation fieldForm rfl

private theorem fieldTwist_generator (i : Fin 5) :
    fieldTwist (fieldForm.specialToProjective (transportedGenerator i)) =
      (fieldForm.specialToProjective (transportedGenerator i))⁻¹ := by
  have h := generator_intertwining i
  have he : intertwiner.val *
      GeneralLinearGroup.map fieldForm.conj.toRingHom (transportedGenerator i).val *
      intertwiner.val⁻¹ = (transportedGenerator i).val⁻¹ := by
    calc
      _ = (transportedGenerator i).val⁻¹ *
          ((transportedGenerator i).val * intertwiner.val *
            GeneralLinearGroup.map fieldForm.conj.toRingHom (transportedGenerator i).val) *
          intertwiner.val⁻¹ := by group
      _ = _ := by rw [h]; group
  apply Subtype.ext
  change (fieldForm.unitaryConj intertwiner
    (fieldActor (fieldForm.specialToProjective (transportedGenerator i)))).val = _
  rw [unitaryConj_apply_val, IsEntrywiseConjugation.apply_val fieldForm fieldActor_entrywise,
    specialToProjective_apply_val, ProjGenLinGroup.map_mk]
  simpa only [map_mul, map_inv, Subgroup.coe_inv, specialToProjective_apply_val] using
    congrArg ProjGenLinGroup.mk he

/-- The already constructed projective embedding with its generator values recorded. -/
private theorem exists_marked_embedding :
    ∃ f : alternatingGroup (Fin 7) →* ProjectiveSpecialUnitaryMatrixGroup fieldForm,
      Function.Injective f ∧ ∀ i,
        f (alternatingSuzukiGenerator 2 i) =
          fieldForm.specialToProjective (transportedGenerator i) := by
  let h : SuzukiPresentedGroup 2 →* ProjectiveSpecialUnitaryMatrixGroup matrixForm :=
    PresentedGroup.toGroup (by rintro _ ⟨r, rfl⟩; exact projective_relator r)
  let e : SuzukiPresentedGroup 2 ≃* alternatingGroup (Fin 7) :=
    MulEquiv.ofBijective (suzukiPresentedProjection 2)
      ⟨suzukiPresentedProjection_injective 2, suzukiPresentedProjection_surjective 2⟩
  let f := h.comp e.symm.toMonoidHom
  have hfgen (i : Fin 5) : f (alternatingSuzukiGenerator 2 i) = projectiveGenerator i := by
    rw [← suzukiPresentedProjection_of]
    change h (e.symm (e (PresentedGroup.of i))) = _
    simp [h]
  have hf : Function.Injective f := by
    let _ : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
    · exact f.ker_eq_bot_iff.mp hbot
    · exfalso
      apply projective_root_ne_one
      rw [← hfgen]
      exact MonoidHom.mem_ker.mp (by rw [htop]; trivial)
  let c := FormTransport.projectiveEquiv matrixForm basisUnit basisUnit_form
  refine ⟨c.toMonoidHom.comp f, c.injective.comp hf, ?_⟩
  intro i
  change c (f (alternatingSuzukiGenerator 2 i)) = _
  rw [hfgen]
  apply Subtype.ext
  rw [FormTransport.projectiveEquiv_apply]
  simp only [projectiveGenerator, specialToProjective_apply_val, transportedGenerator,
    FormTransport.specialEquiv_apply, map_mul, map_inv]

private theorem swap_generator (i : Fin 5) :
    (MulAut.conjNormal (swap (0 : Fin 7) 1)) (alternatingSuzukiGenerator 2 i) =
      (alternatingSuzukiGenerator 2 i)⁻¹ := by
  apply Subtype.ext
  change swap 0 1 * (alternatingSuzukiGenerator 2 i : Perm (Fin 7)) * (swap 0 1)⁻¹ =
    (alternatingSuzukiGenerator 2 i : Perm (Fin 7))⁻¹
  rw [alternatingSuzukiGenerator_val]
  revert i
  decide

theorem exists_field_intertwining :
    ∃ f : alternatingGroup (Fin 7) →* ProjectiveSpecialUnitaryMatrixGroup fieldForm,
      Function.Injective f ∧ ∀ q,
        fieldTwist (f q) = f ((MulAut.conjNormal (swap (0 : Fin 7) 1)) q) := by
  obtain ⟨f, hf, hgen⟩ := exists_marked_embedding
  refine ⟨f, hf, ?_⟩
  have he : fieldTwist.toMonoidHom.comp f =
      f.comp (MulAut.conjNormal (swap (0 : Fin 7) 1)).toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense (alternatingSuzukiGenerator_closure_eq_top 2)
    rintro _ ⟨i, rfl⟩
    change fieldTwist (f (alternatingSuzukiGenerator 2 i)) =
      f ((MulAut.conjNormal (swap (0 : Fin 7) 1)) (alternatingSuzukiGenerator 2 i))
    rw [swap_generator, map_inv, hgen, fieldTwist_generator]
  exact DFunLike.congr_fun he

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer.OddNormalizer
