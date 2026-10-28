module
public import Theory.Representation.AffineNine.CubicBound
public import Theory.SpecificGroups.GL2.ThreeResidualImages.Basic
public meta import Mathlib.Data.Matrix.Basic
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.Algebra.GroupWithZero.Units.Fintype
public meta import Mathlib.Algebra.Field.ZMod
public meta import Theory.Representation.AffineNine.Model
/-!
# Quaternion automizers on the ternary plane

The unique quaternion subgroup of GL₂(3) acts transitively on the eight
nonzero dual vectors. An explicit eight-matrix certificate checks its orbit
of one vector, and composition gives the full orbit statement. Thus any
faithful binary affine-nine representation whose linear image contains this
quaternion group has eight uniform positive nonzero translation weights.
The existing orbit-cover estimate forces cubic ratio strictly greater than two.
The full linear image is allowed to be larger than Q₈.

Source: the needed quaternion obstruction in Aschbacher--Smith 13.3.14(d),
printed p.892. This direct weight proof replaces the appeal to D.2.17.
-/
public section
open Matrix
open scoped MatrixGroups
namespace Representation.AffineNine

private def q0 : SpecialLinear := ⟨!![1, 0; 0, 1], by decide⟩
private def q1 : SpecialLinear := ⟨!![0, 1; 2, 0], by decide⟩
private def q2 : SpecialLinear := ⟨!![2, 0; 0, 2], by decide⟩
private def q3 : SpecialLinear := ⟨!![0, 2; 1, 0], by decide⟩
private def q4 : SpecialLinear := ⟨!![1, 2; 2, 2], by decide⟩
private def q5 : SpecialLinear := ⟨!![2, 2; 2, 1], by decide⟩
private def q6 : SpecialLinear := ⟨!![1, 1; 1, 2], by decide⟩
private def q7 : SpecialLinear := ⟨!![2, 1; 1, 1], by decide⟩
private def qCertificate : Fin 8 → SpecialLinear := ![q0,q1,q2,q3,q4,q5,q6,q7]
private def base : Plane := ![1,0]

private theorem q_certificate_mem (i : Fin 8) :
    SpecialLinearGroup.toGL (qCertificate i) ∈ GeneralLinearGroup.threeQuaternion := by
  rw [GeneralLinearGroup.three_mem_quaternion]
  fin_cases i <;> decide

private theorem q_base_orbit (z : Plane) (hz : z ≠ 0) :
    ∃ i : Fin 8, dualPerm (SpecialLinearGroup.toGL (qCertificate i)) base = z := by
  decide +revert

private theorem dualPerm_mul_eq (g h : LinearGroup) :
    dualPerm (g*h) = dualPerm g * dualPerm h := by
  ext v i
  simp only [dualPerm_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul,
    Equiv.Perm.coe_mul, Function.comp_apply, Matrix.mulVec_mulVec]

private theorem dualPerm_inv_eq (g : LinearGroup) :
    dualPerm g⁻¹ = (dualPerm g)⁻¹ := by
  ext v i
  change (((g⁻¹)⁻¹).val.transpose *ᵥ v) i = (g.val.transpose *ᵥ v) i
  rw [inv_inv]

theorem dualPerm_quaternion_transitive (w z : Plane) (hw : w ≠ 0) (hz : z ≠ 0) :
    ∃ g ∈ GeneralLinearGroup.threeQuaternion, dualPerm g w = z := by
  obtain ⟨a,hwa⟩ := q_base_orbit w hw
  obtain ⟨b,hzb⟩ := q_base_orbit z hz
  refine ⟨SpecialLinearGroup.toGL (qCertificate b) * (SpecialLinearGroup.toGL (qCertificate a))⁻¹,
    GeneralLinearGroup.threeQuaternion.mul_mem (q_certificate_mem b)
      (GeneralLinearGroup.threeQuaternion.inv_mem (q_certificate_mem a)), ?_⟩
  rw [dualPerm_mul_eq,dualPerm_inv_eq,← hwa]
  change dualPerm (SpecialLinearGroup.toGL (qCertificate b))
    ((dualPerm (SpecialLinearGroup.toGL (qCertificate a))).symm
      (dualPerm (SpecialLinearGroup.toGL (qCertificate a)) base)) = z
  exact (congrArg (dualPerm (SpecialLinearGroup.toGL (qCertificate b)))
    ((dualPerm (SpecialLinearGroup.toGL (qCertificate a))).symm_apply_apply base)).trans hzb

variable {L V : Type*} [Group L] [Finite L] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem quaternion_cubicRatio_not_le_two (j : L →* LinearGroup)
    (hj : Function.Injective j) (hQ : GeneralLinearGroup.threeQuaternion ≤ j.range)
    (ρ : Representation (ZMod 2) (Affine j) V) (hf : Function.Injective ρ) :
    ¬ BinaryOffender.cubicRatio ρ ≤ 2 := by
  let coords : CharacterCoordinates (E := algebraicClosureE9) j := {
    equiv := algebraicClosureTranslationCharacterEquiv
    equivariant := fun l w => algebraicClosureTranslationCharacterEquiv_equivariant (j l) w }
  have htrans := characterTransitive_of_coordinates j coords (fun w z hw hz => by
    obtain ⟨g,hg,hgz⟩ := dualPerm_quaternion_transitive w z hw hz
    obtain ⟨l,rfl⟩ := hQ hg
    exact ⟨l,hgz⟩)
  let u := uniformWeights_of_transitive j (ρ.extendScalars algebraicClosureE9)
    ((extendScalars_faithful_iff algebraicClosureE9 ρ).mp hf)
    algebraicClosure_translation_card_ne_zero htrans
  intro h
  obtain ⟨A,hA,_,hd⟩ := (BinaryOffender.cubicRatio_le_nat_iff ρ 2).mp h
  exact (Nat.not_le_of_lt (strict_fixedCodim_of_geometry j hj ρ u A hA)) hd
end Representation.AffineNine
