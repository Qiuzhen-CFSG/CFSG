module

public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Forms
public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Graph
public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Orientation

/-!
# Comparison with the determinant-one spin normalizer

Inside the real general linear group, the source normalizer is the intersection
of the normalizer of the actual faithful spin subgroup with the determinant-one
subgroup. The full endomorphism span makes every intertwiner a positive
similarity, so determinant one forces preservation of the source form.
Conversely, quarter-turn generation of the actual extraspecial automorphism
group forces every form-preserving intertwiner to have determinant one.

Thus form preservation is equivalent to determinant one for every spin
intertwiner. The existing orthogonal normalizer graph projects isomorphically
onto exactly the source normalizer. Conjugation and faithfulness construct its
unique induced automorphism. We also identify the intersection in GL with the
literal relative normalizer inside SL; both isomorphisms preserve the underlying
linear map.

Source: Aschbacher, *Sporadic Groups*, Section 14, Exercise 4.4 on printed
p. 64, and the normalizer `M₁` on printed pp. 147–148.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.LocalC.SourceNormalizer
open TrialitySpin

/-- The source SL normalizer, regarded as a subgroup of the real general linear group. -/
def sourceSLNormalizer : Subgroup (SpinSpace ≃ₗ[ℝ] SpinSpace) :=
  Subgroup.normalizer (spinLinearGroup : Set _) ⊓ (LinearEquiv.det :
    (SpinSpace ≃ₗ[ℝ] SpinSpace) →* ℝˣ).ker

@[simp] theorem mem_sourceSLNormalizer (F : SpinSpace ≃ₗ[ℝ] SpinSpace) :
    F ∈ sourceSLNormalizer ↔ F ∈ Subgroup.normalizer (spinLinearGroup : Set _) ∧
      LinearMap.det F.toLinearMap = 1 := by
  change (F ∈ Subgroup.normalizer (spinLinearGroup : Set _) ∧ LinearEquiv.det F = 1) ↔ _
  rw [← Units.val_inj]
  simp only [LinearEquiv.coe_det, Units.val_one]

/-- Determinant-one normalization preserves the original form, independently of any graph witness. -/
theorem sourceSLNormalizer_preserves_form (F : sourceSLNormalizer) (v w : SpinSpace) :
    bothAxesDomain.form (F.val v) (F.val w) = bothAxesDomain.form v w := by
  obtain ⟨hN, hd⟩ := (mem_sourceSLNormalizer F.val).mp F.prop
  exact form_of_det_one F.val (inducedAutomorphism F.val hN)
    (inducedAutomorphism_intertwines F.val hN) hd v w

/-- The entire source SL normalizer occurs in the existing orthogonal normalizer graph. -/
theorem sourceSLNormalizer_le_spinProjection_range : sourceSLNormalizer ≤ spinProjection.range := by
  intro F hF
  apply (mem_spinProjection_range F).mpr
  exact ⟨((mem_sourceSLNormalizer F).mp hF).1, sourceSLNormalizer_preserves_form ⟨F, hF⟩⟩

/-- The exact determinant information supplied by the form comparison. -/
theorem mem_spinProjection_range_iff_det_sq (F : SpinSpace ≃ₗ[ℝ] SpinSpace) :
    F ∈ spinProjection.range ↔ F ∈ Subgroup.normalizer (spinLinearGroup : Set _) ∧
      (LinearMap.det F.toLinearMap) ^ 2 = 1 := by
  rw [mem_spinProjection_range]
  constructor
  · rintro ⟨hN, hF⟩
    exact ⟨hN, det_sq_of_form F hF⟩
  · rintro ⟨hN, hd⟩
    exact ⟨hN, form_of_det_sq_eq_one F (inducedAutomorphism F hN)
      (inducedAutomorphism_intertwines F hN) hd⟩

/-- Intersecting the orthogonal graph's image with SL gives precisely the source normalizer. -/
theorem spinProjection_range_inf_det_ker :
    spinProjection.range ⊓ (LinearEquiv.det : (SpinSpace ≃ₗ[ℝ] SpinSpace) →* ℝˣ).ker =
      sourceSLNormalizer := by
  apply le_antisymm
  · intro F hF
    exact ⟨((mem_spinProjection_range F).mp hF.1).1, hF.2⟩
  · exact le_inf sourceSLNormalizer_le_spinProjection_range inf_le_right

/-- The unique graph lift of a source SL normalizer element. -/
def sourceSLNormalizerLift : sourceSLNormalizer →* spinNormalizer :=
  spinProjectionEquiv.symm.toMonoidHom.comp
    (Subgroup.inclusion sourceSLNormalizer_le_spinProjection_range)

@[simp] theorem spinProjection_sourceSLNormalizerLift (F : sourceSLNormalizer) :
    spinProjection (sourceSLNormalizerLift F) = F.val := by
  exact congrArg Subtype.val
    (spinProjectionEquiv.apply_symm_apply
      (Subgroup.inclusion sourceSLNormalizer_le_spinProjection_range F))

theorem sourceSLNormalizerLift_injective : Function.Injective sourceSLNormalizerLift := by
  intro F G h
  apply Subtype.ext
  have hp := congrArg spinProjection h
  simpa only [spinProjection_sourceSLNormalizerLift] using hp

/-- For an intertwiner of the actual spin action, preserving the source form is
equivalent to having determinant one. -/
theorem form_iff_det_one (F : SpinSpace ≃ₗ[ℝ] SpinSpace) (α : MulAut Q1Image)
    (hF : ∀ q v, F (SpinAction.imageRepresentation q v) =
      SpinAction.imageRepresentation (α q) (F v)) :
    (∀ v w, bothAxesDomain.form (F v) (F w) = bothAxesDomain.form v w) ↔
      LinearMap.det F.toLinearMap = 1 :=
  ⟨det_one_of_form F α hF, form_of_det_one F α hF⟩

/-- The form comparison for a genuine normalizer element, using the induced
automorphism constructed from conjugation and faithfulness. -/
theorem form_iff_det_one_of_normalizes (F : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (hF : F ∈ Subgroup.normalizer (spinLinearGroup : Set _)) :
    (∀ v w, bothAxesDomain.form (F v) (F w) = bothAxesDomain.form v w) ↔
      LinearMap.det F.toLinearMap = 1 :=
  form_iff_det_one F (inducedAutomorphism F hF) (inducedAutomorphism_intertwines F hF)

/-- The graph projection always has determinant one, by the orientation theorem. -/
@[simp] theorem spinProjection_det_one (f : spinNormalizer) :
    LinearMap.det (spinProjection f).toLinearMap = 1 :=
  det_one_of_form f.val.1 f.val.2 f.prop.1 f.prop.2

/-- Exact membership in the graph projection, expressed by normalization and
determinant one in the real general linear group. -/
theorem mem_spinProjection_range_iff_det_one (F : SpinSpace ≃ₗ[ℝ] SpinSpace) :
    F ∈ spinProjection.range ↔ F ∈ Subgroup.normalizer (spinLinearGroup : Set _) ∧
      LinearMap.det F.toLinearMap = 1 := by
  rw [mem_spinProjection_range]
  exact and_congr_right fun hF => form_iff_det_one_of_normalizes F hF

/-- The graph projects onto precisely the determinant-one source normalizer. -/
theorem spinProjection_range_eq_sourceSLNormalizer :
    spinProjection.range = sourceSLNormalizer := by
  ext F
  rw [mem_spinProjection_range_iff_det_one, mem_sourceSLNormalizer]

/-- The orthogonal normalizer graph and the source SL normalizer are isomorphic
by the actual underlying linear map. -/
def spinNormalizerEquivSourceSLNormalizer : spinNormalizer ≃* sourceSLNormalizer where
  toFun f := ⟨spinProjection f, spinProjection_range_eq_sourceSLNormalizer ▸
    (show spinProjection f ∈ spinProjection.range from ⟨f, rfl⟩)⟩
  invFun := sourceSLNormalizerLift
  left_inv _ := spinProjection_injective (spinProjection_sourceSLNormalizerLift _)
  right_inv F := Subtype.ext (spinProjection_sourceSLNormalizerLift F)
  map_mul' f g := Subtype.ext (map_mul spinProjection f g)

@[simp] theorem spinNormalizerEquivSourceSLNormalizer_val (f : spinNormalizer) :
    (spinNormalizerEquivSourceSLNormalizer f).val = f.val.1 := rfl

@[simp] theorem spinNormalizerEquivSourceSLNormalizer_symm_apply (F : sourceSLNormalizer) :
    spinNormalizerEquivSourceSLNormalizer.symm F = sourceSLNormalizerLift F := rfl

theorem sourceSLNormalizerLift_surjective : Function.Surjective sourceSLNormalizerLift :=
  spinNormalizerEquivSourceSLNormalizer.symm.surjective

/-- The determinant-one subgroup on the actual spin space. -/
def spinSpecialLinearGroup : Subgroup (SpinSpace ≃ₗ[ℝ] SpinSpace) :=
  (LinearEquiv.det : (SpinSpace ≃ₗ[ℝ] SpinSpace) →* ℝˣ).ker

/-- The faithful extraspecial spin image lies in SL. -/
theorem spinLinearGroup_le_specialLinear : spinLinearGroup ≤ spinSpecialLinearGroup := by
  intro F hF
  have hN := spinLinearGroup.le_normalizer hF
  have hd := (form_iff_det_one_of_normalizes F hN).mp (spinLinearGroup_le_isometry hF)
  exact ((mem_sourceSLNormalizer F).mpr ⟨hN, hd⟩).2

/-- The literal relative normalizer in SL used for `M₁` in the source. -/
def relativeSLSpinNormalizer : Subgroup spinSpecialLinearGroup :=
  Subgroup.normalizer (spinLinearGroup.subgroupOf spinSpecialLinearGroup : Set _)

/-- The intersection in GL identifies with the relative normalizer in SL,
without changing the underlying linear map. -/
def sourceSLNormalizerEquivRelativeSLNormalizer :
    sourceSLNormalizer ≃* relativeSLSpinNormalizer where
  toFun F := ⟨⟨F.val, F.prop.2⟩, by
    change (⟨F.val, F.prop.2⟩ : spinSpecialLinearGroup) ∈
      Subgroup.normalizer (spinLinearGroup.subgroupOf spinSpecialLinearGroup : Set _)
    rw [← Subgroup.subgroupOf_normalizer_eq spinLinearGroup_le_specialLinear]
    exact F.prop.1⟩
  invFun F := ⟨F.val.val, by
    refine ⟨?_, F.val.prop⟩
    have h := F.prop
    change F.val ∈ Subgroup.normalizer
      (spinLinearGroup.subgroupOf spinSpecialLinearGroup : Set _) at h
    rw [← Subgroup.subgroupOf_normalizer_eq spinLinearGroup_le_specialLinear] at h
    exact h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem sourceSLNormalizerEquivRelativeSLNormalizer_val (F : sourceSLNormalizer) :
    (sourceSLNormalizerEquivRelativeSLNormalizer F).val.val = F.val := rfl

/-- The graph is the source normalizer inside SL, via its faithful spin map. -/
def spinNormalizerEquivRelativeSLNormalizer : spinNormalizer ≃* relativeSLSpinNormalizer :=
  spinNormalizerEquivSourceSLNormalizer.trans sourceSLNormalizerEquivRelativeSLNormalizer

@[simp] theorem spinNormalizerEquivRelativeSLNormalizer_val (f : spinNormalizer) :
    (spinNormalizerEquivRelativeSLNormalizer f).val.val = f.val.1 := rfl

end Sporadic.Monster.Construction.LocalC.SourceNormalizer
