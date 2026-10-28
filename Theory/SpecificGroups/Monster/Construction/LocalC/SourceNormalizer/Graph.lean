module

public import Theory.SpecificGroups.Monster.Construction.LocalC.Pullback
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The faithful spin subgroup and its orthogonal normalizer

The real spin representation embeds the actual extraspecial quotient `Q1Image`
in the general linear group. Conjugation by a normalizer element induces an
automorphism of this group; transport along the faithful embedding gives the
unique automorphism satisfying the intertwining equation.

Consequently the graph used in `LocalC.Pullback` projects bijectively onto the
normalizing isometries of the faithful spin subgroup. The equivalence with the
normalizer inside the actual form-isometry group respects the underlying
linear maps. No determinant assertion enters this identification.

Source: Aschbacher, *Sporadic Groups*, Section 14 and Section 27,
printed pp. 147–148.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.LocalC.SourceNormalizer
open TrialitySpin

def spinLinearRepresentation : Q1Image →* (SpinSpace ≃ₗ[ℝ] SpinSpace) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ SpinSpace).toMonoidHom.comp
    SpinAction.imageRepresentation.asGroupHom

@[simp] theorem spinLinearRepresentation_apply (q : Q1Image) (v : SpinSpace) :
    spinLinearRepresentation q v = SpinAction.imageRepresentation q v := rfl

theorem spinLinearRepresentation_injective : Function.Injective spinLinearRepresentation := by
  intro a b h
  apply SpinAction.imageRepresentation_faithful
  apply LinearMap.ext
  intro v
  have hv := congrArg (fun f : SpinSpace ≃ₗ[ℝ] SpinSpace => f v) h
  simpa only [spinLinearRepresentation_apply] using hv

/-- The actual faithful extraspecial spin subgroup of the real general linear group. -/
def spinLinearGroup : Subgroup (SpinSpace ≃ₗ[ℝ] SpinSpace) := spinLinearRepresentation.range

def spinImageEquiv : Q1Image ≃* spinLinearGroup :=
  MonoidHom.ofInjective spinLinearRepresentation_injective

/-- Conjugation by a genuine normalizer element, transported to the actual `Q1Image`. -/
def inducedAutomorphism (F : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (hF : F ∈ Subgroup.normalizer (spinLinearGroup : Set _)) : MulAut Q1Image :=
  (spinImageEquiv.trans (spinLinearGroup.normalizerMonoidHom ⟨F, hF⟩)).trans spinImageEquiv.symm

theorem inducedAutomorphism_conjugation (F : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (hF : F ∈ Subgroup.normalizer (spinLinearGroup : Set _)) (q : Q1Image) :
    spinLinearRepresentation (inducedAutomorphism F hF q) =
      F * spinLinearRepresentation q * F⁻¹ := by
  change (spinImageEquiv (spinImageEquiv.symm
    (spinLinearGroup.normalizerMonoidHom ⟨F,hF⟩ (spinImageEquiv q)))).val = _
  rw [spinImageEquiv.apply_symm_apply]
  rfl

theorem inducedAutomorphism_intertwines (F : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (hF : F ∈ Subgroup.normalizer (spinLinearGroup : Set _)) (q : Q1Image) (v : SpinSpace) :
    F (SpinAction.imageRepresentation q v) =
      SpinAction.imageRepresentation (inducedAutomorphism F hF q) (F v) := by
  change F (spinLinearRepresentation q v) =
    spinLinearRepresentation (inducedAutomorphism F hF q) (F v)
  rw [inducedAutomorphism_conjugation]
  simp

theorem intertwiner_normalizes (F : SpinSpace ≃ₗ[ℝ] SpinSpace) (α : MulAut Q1Image)
    (hF : ∀ q v, F (SpinAction.imageRepresentation q v) =
      SpinAction.imageRepresentation (α q) (F v)) :
    F ∈ Subgroup.normalizer (spinLinearGroup : Set _) := by
  have hc (q : Q1Image) : F * spinLinearRepresentation q * F⁻¹ =
      spinLinearRepresentation (α q) := by
    apply LinearEquiv.ext
    intro v
    change F (SpinAction.imageRepresentation q (F.symm v)) =
      SpinAction.imageRepresentation (α q) v
    rw [hF, F.apply_symm_apply]
  intro g
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨α q, (hc q).symm⟩
  · rintro ⟨q, hq⟩
    refine ⟨α.symm q, ?_⟩
    have h := hc (α.symm q)
    rw [α.apply_symm_apply, hq] at h
    exact mul_right_cancel (mul_left_cancel h)

/-- Normalization is equivalent to a unique intertwining automorphism. -/
theorem normalizes_iff_existsUnique (F : SpinSpace ≃ₗ[ℝ] SpinSpace) :
    F ∈ Subgroup.normalizer (spinLinearGroup : Set _) ↔ ∃! α : MulAut Q1Image,
      ∀ q v, F (SpinAction.imageRepresentation q v) =
        SpinAction.imageRepresentation (α q) (F v) := by
  constructor
  · intro hF
    refine ⟨inducedAutomorphism F hF, inducedAutomorphism_intertwines F hF, ?_⟩
    intro α hα
    apply MulEquiv.ext
    intro q
    apply SpinAction.imageRepresentation_faithful
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := F.surjective v
    rw [← hα, ← inducedAutomorphism_intertwines]
  · rintro ⟨α, hα, _⟩
    exact intertwiner_normalizes F α hα

/-- Forget the induced automorphism in the existing orthogonal normalizer graph. -/
def spinProjection : spinNormalizer →* (SpinSpace ≃ₗ[ℝ] SpinSpace) :=
  (MonoidHom.fst _ _).comp spinNormalizer.subtype

theorem spinProjection_injective : Function.Injective spinProjection :=
  fun _ _ h => spinNormalizer_ext h

/-- Exact image of the graph: the normalizing isometries of the faithful spin subgroup. -/
theorem mem_spinProjection_range (F : SpinSpace ≃ₗ[ℝ] SpinSpace) :
    F ∈ spinProjection.range ↔ F ∈ Subgroup.normalizer (spinLinearGroup : Set _) ∧
      ∀ v w, bothAxesDomain.form (F v) (F w) = bothAxesDomain.form v w := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨intertwiner_normalizes f.val.1 f.val.2 f.prop.1, f.prop.2⟩
  · rintro ⟨hN, hB⟩
    exact ⟨⟨(F, inducedAutomorphism F hN),
      inducedAutomorphism_intertwines F hN, hB⟩, rfl⟩

/-- The graph is isomorphic to its faithful image in the general linear group. -/
def spinProjectionEquiv : spinNormalizer ≃* spinProjection.range :=
  MonoidHom.ofInjective spinProjection_injective

/-- The isometry group of the fixed positive spin form, inside the real linear group. -/
def spinIsometryGroup : Subgroup (SpinSpace ≃ₗ[ℝ] SpinSpace) where
  carrier F := ∀ v w, bothAxesDomain.form (F v) (F w) = bothAxesDomain.form v w
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro F G hF hG v w
    change bothAxesDomain.form (F (G v)) (F (G w)) = _
    rw [hF, hG]
  inv_mem' := by
    intro F hF v w
    change bothAxesDomain.form (F.symm v) (F.symm w) = bothAxesDomain.form v w
    have h := hF (F.symm v) (F.symm w)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem spinLinearGroup_le_isometry : spinLinearGroup ≤ spinIsometryGroup := by
  rintro F ⟨q, rfl⟩
  exact SpinAction.imageRepresentation_isometry q

/-- The actual relative normalizer of the faithful spin subgroup in its form-isometry group. -/
def orthogonalSpinNormalizer : Subgroup spinIsometryGroup :=
  Subgroup.normalizer (spinLinearGroup.subgroupOf spinIsometryGroup : Set _)

/-- Regard an element of the normalizer graph as an element of the relative normalizer. -/
def graphToOrthogonalNormalizer : spinNormalizer →* orthogonalSpinNormalizer where
  toFun f := ⟨⟨f.val.1, f.prop.2⟩, by
    change (⟨f.val.1, f.prop.2⟩ : spinIsometryGroup) ∈
      Subgroup.normalizer (spinLinearGroup.subgroupOf spinIsometryGroup : Set _)
    rw [← Subgroup.subgroupOf_normalizer_eq spinLinearGroup_le_isometry]
    exact intertwiner_normalizes f.val.1 f.val.2 f.prop.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem graphToOrthogonalNormalizer_bijective : Function.Bijective graphToOrthogonalNormalizer := by
  constructor
  · intro f g h
    apply spinNormalizer_ext
    exact congrArg (fun p : orthogonalSpinNormalizer => p.val.val) h
  · intro F
    have hN : F.val.val ∈ Subgroup.normalizer (spinLinearGroup : Set _) := by
      have h := F.prop
      change F.val ∈ Subgroup.normalizer
        (spinLinearGroup.subgroupOf spinIsometryGroup : Set _) at h
      rw [← Subgroup.subgroupOf_normalizer_eq spinLinearGroup_le_isometry] at h
      exact h
    refine ⟨⟨(F.val.val, inducedAutomorphism F.val.val hN),
      inducedAutomorphism_intertwines F.val.val hN, F.val.prop⟩, ?_⟩
    rfl

/-- The normalizer graph is the actual orthogonal normalizer of the faithful spin subgroup. -/
def spinNormalizerEquivOrthogonalNormalizer : spinNormalizer ≃* orthogonalSpinNormalizer :=
  MulEquiv.ofBijective graphToOrthogonalNormalizer graphToOrthogonalNormalizer_bijective

@[simp] theorem spinNormalizerEquivOrthogonalNormalizer_val (f : spinNormalizer) :
    (spinNormalizerEquivOrthogonalNormalizer f).val.val = f.val.1 := rfl

end Sporadic.Monster.Construction.LocalC.SourceNormalizer
