module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SpinIrreducible
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Central.End

/-!
# Similarities of the faithful real spin module

The concrete extraspecial spin operators span all real endomorphisms. Thus
an invariant bilinear form differs from the source form by a scalar: use the
nondegenerate form to turn it into a commuting endomorphism, then the full
endomorphism span to make that endomorphism central. Pulling the source form
back through a normalizing intertwiner gives a positive scalar. Taking Gram
matrix determinants shows that this scalar is one exactly when the square of
the intertwiner's determinant is one.

In particular, every determinant-one normalizer element preserves the original
form. This does not yet exclude orientation-reversing normalizer elements;
that is the remaining implication in the comparison with the source SL
normalizer.

Source: Aschbacher, *Sporadic Groups*, Section 14, Exercise 4.4 on printed
p. 64, and the spin normalizer on printed pp. 147–148.
-/

public section
noncomputable section
open Module
namespace Sporadic.Monster.Construction.LocalC.SourceNormalizer
open TrialitySpin

private theorem invariant_form_scalar {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] (ρ : Representation ℝ G V)
    (hspan : Submodule.span ℝ (Set.range (ρ : G → End ℝ V)) = ⊤)
    (B D : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (hBi : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    (hDi : ∀ g v w, D (ρ g v) (ρ g w) = D v w) :
    ∃ c : ℝ, D = c • B := by
  let T : End ℝ V := (B.toDual hB).symm.toLinearMap.comp D
  have hT (v w : V) : B (T v) w = D v w :=
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) _ _
  have hcomm (g : G) : T * ρ g = ρ g * T := by
    ext v
    apply (B.toDual hB).injective
    ext w
    change B (T (ρ g v)) w = B (ρ g (T v)) w
    obtain ⟨w, rfl⟩ :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ V (ρ.asGroupHom g)).surjective w
    change B (T (ρ g v)) (ρ g w) = B (ρ g (T v)) (ρ g w)
    rw [hT, hDi, hBi, hT]
  have hcomm_all (S : End ℝ V) : T * S = S * T := by
    have hS : S ∈ Submodule.span ℝ (Set.range (ρ : G → End ℝ V)) := by
      rw [hspan]; trivial
    induction hS using Submodule.span_induction with
    | mem S h => obtain ⟨g, rfl⟩ := h; exact hcomm g
    | zero => simp
    | add S U _ _ hS hU => simp only [mul_add, add_mul, hS, hU]
    | smul c S _ hS => simp only [mul_smul_comm, smul_mul_assoc, hS]
  have hcenter : T ∈ Subalgebra.center ℝ (End ℝ V) := by
    rw [Subalgebra.mem_center_iff]
    intro S
    exact (hcomm_all S).symm
  obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff ℝ).mp hcenter
  refine ⟨c, ?_⟩
  ext v w
  rw [← hT, hc]
  simp

/-- The concrete spin operators span all real endomorphisms. -/
theorem spin_span :
    Submodule.span ℝ (Set.range (SpinAction.imageRepresentation : Q1Image → End ℝ SpinSpace)) = ⊤ := by
  let : IsExtraspecial 2 Q1Image := Q1Image_extraspecial
  have hz : q1ImageCenterGenerator ∈ Subgroup.center Q1Image := by
    rw [Q1Image_center]
    exact Subgroup.mem_zpowers _
  exact Representation.span_range_eq_top_of_extraspecial_two_finrank_4096
    SpinAction.imageRepresentation hz q1ImageCenterGenerator_ne_one
    SpinAction.imageRepresentation_center Q1Image_card finrank_spinSpace

private theorem form_nondegenerate : bothAxesDomain.form.Nondegenerate := by
  constructor
  · intro v hv
    by_contra h
    exact (ne_of_gt (bothAxesDomain.form_pos v h)) (hv v)
  · intro v hv
    by_contra h
    exact (ne_of_gt (bothAxesDomain.form_pos v h)) (hv v)

/-- An intertwiner of the spin group is a positive similarity of its source form. -/
theorem intertwiner_similarity (F : SpinSpace ≃ₗ[ℝ] SpinSpace) (α : MulAut Q1Image)
    (hF : ∀ q v, F (SpinAction.imageRepresentation q v) =
      SpinAction.imageRepresentation (α q) (F v)) :
    ∃ c : ℝ, 0 < c ∧ bothAxesDomain.form.comp F.toLinearMap F.toLinearMap =
      c • bothAxesDomain.form := by
  obtain ⟨c, hc⟩ := invariant_form_scalar SpinAction.imageRepresentation spin_span
    bothAxesDomain.form (bothAxesDomain.form.comp F.toLinearMap F.toLinearMap)
    form_nondegenerate SpinAction.imageRepresentation_isometry (by
      intro q v w
      change bothAxesDomain.form (F (SpinAction.imageRepresentation q v))
        (F (SpinAction.imageRepresentation q w)) = bothAxesDomain.form (F v) (F w)
      rw [hF, hF, SpinAction.imageRepresentation_isometry])
  refine ⟨c, ?_, hc⟩
  have : Nontrivial SpinSpace := (Module.finrank_pos_iff (R := ℝ)).mp (by rw [finrank_spinSpace]; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : SpinSpace)
  have he := congrArg (fun B : LinearMap.BilinForm ℝ SpinSpace => B v v) hc
  change bothAxesDomain.form (F v) (F v) = c * bothAxesDomain.form v v at he
  have hp := bothAxesDomain.form_pos (F v) (by simpa using hv)
  rw [he] at hp
  exact (mul_pos_iff.mp hp).resolve_right (fun h => (not_lt_of_ge (le_of_lt
    (bothAxesDomain.form_pos v hv))) h.2) |>.1

private theorem similarity_det (F : SpinSpace ≃ₗ[ℝ] SpinSpace) (c : ℝ)
    (hc : bothAxesDomain.form.comp F.toLinearMap F.toLinearMap = c • bothAxesDomain.form) :
    (LinearMap.det F.toLinearMap) ^ 2 = c ^ 4096 := by
  classical
  let b := Module.finBasis ℝ SpinSpace
  have h := congrArg (fun B : LinearMap.BilinForm ℝ SpinSpace =>
    (LinearMap.BilinForm.toMatrix b B).det) hc
  rw [LinearMap.BilinForm.toMatrix_comp b b] at h
  simp only [Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix,
    map_smul, Matrix.det_smul, Fintype.card_fin, finrank_spinSpace] at h
  have hn := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp form_nondegenerate
  apply mul_right_cancel₀ hn
  nlinarith only [h]

/-- A spin intertwiner of determinant squared one preserves the original form. -/
theorem form_of_det_sq_eq_one (F : SpinSpace ≃ₗ[ℝ] SpinSpace) (α : MulAut Q1Image)
    (hF : ∀ q v, F (SpinAction.imageRepresentation q v) =
      SpinAction.imageRepresentation (α q) (F v))
    (hdet : (LinearMap.det F.toLinearMap) ^ 2 = 1) :
    ∀ v w, bothAxesDomain.form (F v) (F w) = bothAxesDomain.form v w := by
  obtain ⟨c, hc, hform⟩ := intertwiner_similarity F α hF
  have hd := similarity_det F c hform
  rw [hdet] at hd
  have hc1 : c = 1 := (pow_left_inj₀ hc.le (by norm_num) (by norm_num : (4096 : ℕ) ≠ 0)).mp
    (by simpa using hd.symm)
  rw [hc1, one_smul] at hform
  intro v w
  exact congrArg (fun B : LinearMap.BilinForm ℝ SpinSpace => B v w) hform

/-- A spin-form isometry has determinant either sign of one. -/
theorem det_sq_of_form (F : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (hF : ∀ v w, bothAxesDomain.form (F v) (F w) = bothAxesDomain.form v w) :
    (LinearMap.det F.toLinearMap) ^ 2 = 1 := by
  have h := similarity_det F 1 (by ext v w; exact (hF v w).trans (by simp))
  simpa using h
/-- Exact comparison prior to the additional orientation theorem. -/
theorem form_iff_det_sq_eq_one (F : SpinSpace ≃ₗ[ℝ] SpinSpace) (α : MulAut Q1Image)
    (hF : ∀ q v, F (SpinAction.imageRepresentation q v) =
      SpinAction.imageRepresentation (α q) (F v)) :
    (∀ v w, bothAxesDomain.form (F v) (F w) = bothAxesDomain.form v w) ↔
      (LinearMap.det F.toLinearMap) ^ 2 = 1 :=
  ⟨det_sq_of_form F, form_of_det_sq_eq_one F α hF⟩

/-- Determinant one forces preservation of the original spin form. -/
theorem form_of_det_one (F : SpinSpace ≃ₗ[ℝ] SpinSpace) (α : MulAut Q1Image)
    (hF : ∀ q v, F (SpinAction.imageRepresentation q v) =
      SpinAction.imageRepresentation (α q) (F v))
    (hdet : LinearMap.det F.toLinearMap = 1) :
    ∀ v w, bothAxesDomain.form (F v) (F w) = bothAxesDomain.form v w :=
  form_of_det_sq_eq_one F α hF (by rw [hdet]; norm_num)

end Sporadic.Monster.Construction.LocalC.SourceNormalizer
