module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.Endpoint
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.Collection
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.WeylVerification.MatrixTransport
import Mathlib.Tactic.Group

/-!
# The literal full-Ree second Weyl equations

The checked first-root conjugation and Parrott relations (I), (VI), and
(VIII) give the reflection action on all ten radical generators. Squaring
gives the last three source roots, and involutivity gives the reverse
conjugations. Everything is transported through the actual marked Atlas
embedding and the coordinate amalgam inclusion.

This discharges exactly the relation contract consumed by
`separator_extends_of_weyl_relations`, without an extension assumption.
Source: Shinoda (1975), pp.81–83; Parrott (1972), p.683;
Aschbacher–Smith F.1.11–12, pp.262–263.
-/

public section
noncomputable section

namespace Tits.AmalgamRigidity.FullRee.SecondExtension
open ReeTwo ParabolicMarkedComparison
open ReeF4.Parabolics.Binary.FixedGeometry

private abbrev r : ReeF4.Model 0 := weylLift 0 .linear

private theorem root_five : Ambient.root 5 = Ambient.root 1 ^ 2 := rfl
private theorem root_eight : Ambient.root 8 = Ambient.root 3 ^ 2 := rfl
private theorem root_nine : Ambient.root 9 = Ambient.root 2 ^ 2 := rfl

attribute [local irreducible] Ambient.root Ambient.rootOne
private abbrev c := MulAut.conj r

private theorem source_square : r ^ 2 = 1 := by
  have h := atlas1600ParrottAssignment_relations .i_r8
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of] at h
  simpa only [map_pow, map_one, Ambient.atlas_generator, Ambient.parrottWord] using
    congrArg ExceptionalParabolics.FullRee.atlasEmbedding h

private theorem source_inverse : r⁻¹ = r :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using source_square)

private theorem source_cube : (r * Ambient.root 0) ^ 3 = 1 := by
  have h := atlas1600ParrottAssignment_relations .vi_r8_s8
  simp only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of] at h
  simpa only [map_pow, map_mul, map_one, Ambient.atlas_generator, Ambient.parrottWord] using
    congrArg ExceptionalParabolics.FullRee.atlasEmbedding h

private theorem conjugation_twice (x : ReeF4.Model 0) : c (c x) = x := by
  change r * (r * x * r⁻¹) * r⁻¹ = x
  calc
    _ = (r * r) * x * (r * r)⁻¹ := by group
    _ = x := by rw [← pow_two, source_square]; simp

private theorem conjugation_reverse {x y : ReeF4.Model 0} (h : c x = y) : c y = x := by
  rw [← h, conjugation_twice]

private theorem conjugate_four : c (Ambient.root 4) = Ambient.root 6 := by
  have h := atlas1600ParrottAssignment_relations .viii_s2
  simp only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of] at h
  have hm := congrArg ExceptionalParabolics.FullRee.atlasEmbedding (mul_inv_eq_one.mp h)
  simpa only [map_mul, Ambient.atlas_generator, Ambient.parrottWord,
    c, MulAut.conj_apply, source_inverse] using hm

private theorem conjugate_seven : c (Ambient.root 7) = Ambient.root 7 := by
  have h := atlas1600ParrottAssignment_relations .viii_s4
  simp only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of] at h
  have hm := congrArg ExceptionalParabolics.FullRee.atlasEmbedding (mul_inv_eq_one.mp h)
  simpa only [map_mul, Ambient.atlas_generator, Ambient.parrottWord,
    c, MulAut.conj_apply, source_inverse] using hm

private theorem conjugate_three (h0 : c Ambient.rootOne = Ambient.root 1) :
    c (Ambient.root 3) = Ambient.root 2 := by
  have h := atlas1600ParrottAssignment_relations .viii_s3
  simp only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of] at h
  have hm := congrArg ExceptionalParabolics.FullRee.atlasEmbedding (mul_inv_eq_one.mp h)
  have hprod : c (Ambient.rootOne * Ambient.root 3) =
      Ambient.root 1 * Ambient.root 2 := by
    change r * (Ambient.rootOne * Ambient.root 3) * r⁻¹ = _
    rw [source_inverse]
    simpa only [map_mul, Ambient.atlas_generator, Ambient.parrottWord,
      mul_assoc, inv_mul_cancel_left] using hm
  rw [map_mul, h0] at hprod
  exact mul_left_cancel hprod

/-- All twelve Weyl equations in the literal full second endpoint. -/
theorem weyl_relations : WeylRelations inclusion reflection := by
  have h0 : c Ambient.rootOne = Ambient.root 1 :=
    WeylVerification.ambient_reflection_rootOne
  have h1 := conjugation_reverse h0
  have h4 := conjugate_four
  have h6 := conjugation_reverse h4
  have h7 := conjugate_seven
  have h3 := conjugate_three h0
  have h2 := conjugation_reverse h3
  have h5 : c (Ambient.root 5) = Ambient.rootOne ^ 2 := by
    rw [root_five, map_pow, h1]
  have h8 : c (Ambient.root 8) = Ambient.root 9 := by
    rw [root_eight, root_nine, map_pow, h3]
  have h9 := conjugation_reverse h8
  refine ⟨?_, ?_, ?_⟩
  · apply Subtype.ext
    exact source_square
  · apply Subtype.ext
    change ((inclusion (SylowModel.root 0) : ReeF4.Model 0) * r) ^ 3 = 1
    rw [inclusion_root]
    have he : (Ambient.root 0 * r) ^ 3 =
        r⁻¹ * (r * Ambient.root 0) ^ 3 * r := by
      simp only [pow_succ, pow_zero]
      group
    rw [he, source_cube]
    simp
  · intro i
    apply Subtype.ext
    change r * (inclusion (radicalGenerator i) : ReeF4.Model 0) * r⁻¹ =
      (inclusion (weylImage i) : ReeF4.Model 0)
    fin_cases i
    · change r * (inclusion SylowModel.rootOne : ReeF4.Model 0) * r⁻¹ =
        (inclusion (SylowModel.root 1) : ReeF4.Model 0)
      simpa only [c, MulAut.conj_apply, inclusion_rootOne, inclusion_root] using h0
    · change r * (inclusion (SylowModel.root 1) : ReeF4.Model 0) * r⁻¹ =
        (inclusion SylowModel.rootOne : ReeF4.Model 0)
      simpa only [c, MulAut.conj_apply, inclusion_rootOne, inclusion_root] using h1
    · change r * (inclusion (SylowModel.root 2) : ReeF4.Model 0) * r⁻¹ =
        (inclusion (SylowModel.root 3) : ReeF4.Model 0)
      simpa only [c, MulAut.conj_apply, inclusion_root] using h2
    · change r * (inclusion (SylowModel.root 3) : ReeF4.Model 0) * r⁻¹ =
        (inclusion (SylowModel.root 2) : ReeF4.Model 0)
      simpa only [c, MulAut.conj_apply, inclusion_root] using h3
    · change r * (inclusion (SylowModel.root 4) : ReeF4.Model 0) * r⁻¹ =
        (inclusion (SylowModel.root 6) : ReeF4.Model 0)
      simpa only [c, MulAut.conj_apply, inclusion_root] using h4
    · change r * (inclusion (SylowModel.root 5) : ReeF4.Model 0) * r⁻¹ =
        (inclusion (SylowModel.rootOne ^ 2) : ReeF4.Model 0)
      simpa only [c, MulAut.conj_apply, map_pow, Subgroup.coe_pow, inclusion_root, inclusion_rootOne] using h5
    · change r * (inclusion (SylowModel.root 6) : ReeF4.Model 0) * r⁻¹ =
        (inclusion (SylowModel.root 4) : ReeF4.Model 0)
      simpa only [c, MulAut.conj_apply, inclusion_root] using h6
    · change r * (inclusion (SylowModel.root 7) : ReeF4.Model 0) * r⁻¹ =
        (inclusion (SylowModel.root 7) : ReeF4.Model 0)
      simpa only [c, MulAut.conj_apply, inclusion_root] using h7
    · change r * (inclusion (SylowModel.root 8) : ReeF4.Model 0) * r⁻¹ =
        (inclusion (SylowModel.root 9) : ReeF4.Model 0)
      simpa only [c, MulAut.conj_apply, inclusion_root] using h8
    · change r * (inclusion (SylowModel.root 9) : ReeF4.Model 0) * r⁻¹ =
        (inclusion (SylowModel.root 8) : ReeF4.Model 0)
      simpa only [c, MulAut.conj_apply, inclusion_root] using h9
end Tits.AmalgamRigidity.FullRee.SecondExtension
