module
public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines.Rotations
public import Theory.GroupTheory.PPerfectHom

/-!
# The normalizer of the binary orthogonal residual

The independent cubic rotations recover the quadratic form: a nonzero vector
is nonsingular exactly when a nonidentity rotation fixes it. Hence their full
linear normalizer is the actual orthogonal group. Its two-residual consists
of rotations, so every two-perfect normalizing actor centralizes the residual.

This is the paired-plane calculation consumed in original 13.2.14, without
assuming that an external normalizer already preserves the quadratic form.
Source: Aschbacher--Smith, printed p.883; the natural O₄⁺(2) action in
13.2.8(3), p.880.
-/

@[expose] public section
open Subgroup Theory.AlgebraicGroup
open scoped IsMulCommutative
namespace OrthogonalFourBinary.TerminalLines
abbrev LinearActor := Space ≃ₗ[F] Space

def linearRotations : Subgroup LinearActor := rotations.map IsometryGroup.subtype

private theorem form_one_iff_rotation_fixed (v : Space) :
    form v = 1 ↔ v ≠ 0 ∧ ∃ i : RotationCode, i ≠ 1 ∧ rotation i v = v := by
  exact (show ∀ v : Space, form v = 1 ↔ v ≠ 0 ∧
    ∃ i : RotationCode, i ≠ 1 ∧ rotation i v = v from by decide +kernel) v

private theorem form_one_iff_linearRotation_fixed (v : Space) :
    form v = 1 ↔ v ≠ 0 ∧ ∃ r ∈ linearRotations, r ≠ 1 ∧ r v = v := by
  rw [form_one_iff_rotation_fixed]
  constructor
  · rintro ⟨hv,i,hi,hfix⟩
    refine ⟨hv,(rotationHom i : LinearActor), ?_, ?_,hfix⟩
    · exact mem_map_of_mem IsometryGroup.subtype (show rotationHom i ∈ rotations from ⟨i,rfl⟩)
    · intro he
      exact hi (rotationHom_injective ((Subtype.ext he).trans (map_one rotationHom).symm))
  · rintro ⟨hv,r,⟨s,⟨i,rfl⟩,rfl⟩,hr,hfix⟩
    refine ⟨hv,i,?_,hfix⟩
    rintro rfl
    exact hr (congrArg Subtype.val (map_one rotationHom))

private theorem normalizer_preserves_form_one (a : LinearActor)
    (ha : a ∈ normalizer (linearRotations : Set LinearActor)) {v : Space}
    (hv : form v = 1) : form (a v) = 1 := by
  obtain ⟨hv0,r,hr,hr1,hfix⟩ := (form_one_iff_linearRotation_fixed v).mp hv
  apply (form_one_iff_linearRotation_fixed (a v)).mpr
  refine ⟨fun he => hv0 (a.injective (he.trans a.map_zero.symm)),
    a*r*a⁻¹,(mem_normalizer_iff.mp ha r).mp hr,?_,?_⟩
  · intro he
    apply hr1
    have hh := congrArg (fun x : LinearActor => a⁻¹*x*a) he
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one,one_mul] using hh
  · change a (r (a.symm (a v))) = a v
    rw [LinearEquiv.symm_apply_apply,hfix]

/-- The two independent cubic rotations intrinsically recover the quadratic form. -/
theorem linearRotations_normalizer_le_isometry :
    normalizer (linearRotations : Set LinearActor) ≤ IsometryGroup := by
  intro a ha
  apply (mem_quadraticIsometrySubgroup form a).mpr
  intro v
  have he : form (a v) = 1 ↔ form v = 1 := by
    constructor
    · intro hv
      have hh := normalizer_preserves_form_one a⁻¹ ((normalizer _).inv_mem ha) hv
      change form (a.symm (a v)) = 1 at hh
      simpa only [LinearEquiv.symm_apply_apply] using hh
    · exact normalizer_preserves_form_one a ha
  exact (show ∀ x y : F, (x = 1 ↔ y = 1) → x = y from by decide) _ _ he

/-- The full linear normalizer of the actual cubic residual is O₄⁺(2). -/
theorem linearRotations_normalizer_eq_isometry :
    normalizer (linearRotations : Set LinearActor) = IsometryGroup := by
  apply le_antisymm linearRotations_normalizer_le_isometry
  have hh := rotations.le_normalizer_map IsometryGroup.subtype
  rw [normalizer_eq_top, ←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh

/-- A two-perfect linear actor normalizing the cubic residual has image in that residual. -/
theorem twoPerfect_linear_normalizer_le_rotations
    {A : Type*} [Group A] (hA : IsPPerfect 2 A) (f : A →* LinearActor)
    (hn : f.range ≤ normalizer (linearRotations : Set LinearActor)) :
    f.range ≤ linearRotations := by
  let g := f.codRestrict IsometryGroup (fun a =>
    linearRotations_normalizer_le_isometry (hn ⟨a,rfl⟩))
  have hg : g.range ≤ pResidual 2 IsometryGroup := by
    have hh := map_pResidual_le 2 g
    rw [(pResidual_eq_top_iff 2 A).mpr hA, ← MonoidHom.range_eq_map] at hh
    exact hh
  rintro r ⟨a,rfl⟩
  exact mem_map_of_mem IsometryGroup.subtype (residual_eq_rotations ▸ hg ⟨a,rfl⟩)

/-- The two-perfect normalizer acts trivially on the residual by conjugation. -/
theorem twoPerfect_linear_normalizer_centralizes_rotations
    {A : Type*} [Group A] (hA : IsPPerfect 2 A) (f : A →* LinearActor)
    (hn : f.range ≤ normalizer (linearRotations : Set LinearActor)) :
    f.range ≤ centralizer (linearRotations : Set LinearActor) := by
  have hc : IsMulCommutative linearRotations := by
    unfold linearRotations
    infer_instance
  let := hc
  intro a ha r hr
  exact congrArg linearRotations.subtype
    (mul_comm (⟨r,hr⟩ : linearRotations)
      ⟨a,twoPerfect_linear_normalizer_le_rotations hA f hn ha⟩)

end OrthogonalFourBinary.TerminalLines
