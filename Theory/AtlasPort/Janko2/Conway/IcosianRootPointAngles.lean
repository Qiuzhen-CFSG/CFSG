/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootPointAngles.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointNormWord
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisRootGeometry

/-!
# IcosianRootPointAngles

The normalized norm of the Hermitian pairing defines an intrinsic angle on root lines.
Unit invariance makes it independent of root representatives, with orthogonality characterized by angle zero.

Source: Gerald Höhn, `Atlas/Conway/IcosianRootPointAngles.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Quaternion

/-- The normalized quaternionic Hermitian angle for norm-two roots. -/
def icosianRootAngle (r s : IcosianRoot) : GoldenRational :=
  icosianNorm (icosianHermitian (icosianCoordinateEmbedding r.val)
    (icosianCoordinateEmbedding s.val)) / 4

theorem icosianRootAngle_normalized (r s : IcosianRoot) :
    icosianRootAngle r s =
      icosianNorm (icosianHermitian (icosianCoordinateEmbedding r.val)
        (icosianCoordinateEmbedding s.val)) /
      ((icosianHermitian (icosianCoordinateEmbedding r.val)
        (icosianCoordinateEmbedding r.val)).re *
       (icosianHermitian (icosianCoordinateEmbedding s.val)
        (icosianCoordinateEmbedding s.val)).re) := by
  rw [r.property.2,s.property.2]
  simp only [QuaternionAlgebra.re_ofNat]
  norm_num [icosianRootAngle]

theorem icosianRootAngle_right_units (r s : IcosianRoot) (u v : icosianNormOneGroup) :
    icosianRootAngle (icosianRootRightUnit r u) (icosianRootRightUnit s v) = icosianRootAngle r s := by
  change icosianNorm (icosianHermitian
    (icosianRightMul (icosianCoordinateEmbedding r.val) u.val.val)
    (icosianRightMul (icosianCoordinateEmbedding s.val) v.val.val)) / 4 = _
  rw [icosianHermitian_rightMul_left,icosianHermitian_rightMul_right]
  simp only [icosianNorm, map_mul,Quaternion.normSq_star]
  change (icosianNorm u.val.val * (icosianNorm (icosianHermitian
    (icosianCoordinateEmbedding r.val) (icosianCoordinateEmbedding s.val)) *
    icosianNorm v.val.val)) / 4 = _
  rw [icosianNormOneGroup_norm,icosianNormOneGroup_norm,one_mul,mul_one]
  rfl

theorem icosianRootAngle_of_same_points (r s a b : IcosianRoot)
    (ha : icosianRootPoint a = icosianRootPoint r)
    (hb : icosianRootPoint b = icosianRootPoint s) :
    icosianRootAngle a b = icosianRootAngle r s := by
  obtain ⟨u,rfl⟩ := (icosianRootPoint_eq_iff r a).mp ha
  obtain ⟨v,rfl⟩ := (icosianRootPoint_eq_iff s b).mp hb
  exact icosianRootAngle_right_units r s u v

/-- Intrinsic angle on actual quaternionic root lines. -/
def icosianRootPointAngle (p q : IcosianRootPoint) : GoldenRational :=
  icosianRootAngle p.property.choose q.property.choose

theorem icosianRootPointAngle_toPoint (r s : IcosianRoot) :
    icosianRootPointAngle (icosianRootToPoint r) (icosianRootToPoint s) = icosianRootAngle r s :=
  icosianRootAngle_of_same_points r s _ _ (icosianRootToPoint r).property.choose_spec
    (icosianRootToPoint s).property.choose_spec

theorem icosianRootPointAngle_smul (g : icosianHermitianGroup) (p q : IcosianRootPoint) :
    icosianRootPointAngle (g • p) (g • q) = icosianRootPointAngle p q := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  obtain ⟨s,rfl⟩ := icosianRootToPoint_surjective q
  rw [← icosianRootToPoint_smul,← icosianRootToPoint_smul,
    icosianRootPointAngle_toPoint,icosianRootPointAngle_toPoint]
  change icosianRootAngle (icosianHermitianRoot g r) (icosianHermitianRoot g s) = _
  unfold icosianRootAngle
  rw [icosianHermitianRoot_embedding,icosianHermitianRoot_embedding,g.property.2.1]

theorem icosianRootPointAngle_symm (p q : IcosianRootPoint) :
    icosianRootPointAngle p q = icosianRootPointAngle q p := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  obtain ⟨s,rfl⟩ := icosianRootToPoint_surjective q
  rw [icosianRootPointAngle_toPoint,icosianRootPointAngle_toPoint]
  unfold icosianRootAngle
  rw [← icosianHermitian_star]
  simp only [icosianNorm,Quaternion.normSq_star]

theorem icosianRootPointAngle_self (p : IcosianRootPoint) : icosianRootPointAngle p p = 1 := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  rw [icosianRootPointAngle_toPoint]
  unfold icosianRootAngle
  rw [r.property.2]
  decide +kernel

theorem icosianRootPointAngle_zero_iff (p q : IcosianRootPoint) :
    icosianRootPointAngle p q = 0 ↔ IcosianRootPointOrthogonal p q := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  obtain ⟨s,rfl⟩ := icosianRootToPoint_surjective q
  rw [icosianRootPointAngle_toPoint,icosianRootPointOrthogonal_iff]
  unfold icosianRootAngle
  rw [div_eq_zero_iff]
  have h4 : (4 : GoldenRational) ≠ 0 := by decide +kernel
  simp only [h4,or_false,icosianNorm_eq_zero]

theorem icosianRootPointAngle_axis (i : Fin 3) (p : IcosianRootPoint) :
    icosianRootPointAngle (icosianRootAxisPoint i) p =
      goldenIntegerToRational (icosianRootPointNormWord p i) / 4 := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  change icosianRootPointAngle (icosianRootToPoint (icosianAxisRoot (i,1))) _ = _
  rw [icosianRootPointAngle_toPoint,icosianRootPointNormWord_toPoint]
  unfold icosianRootAngle
  rw [icosianAxisRoot_hermitian]
  simp only [icosianRootNormWord,icosianIntegralNorm_spec]
  rfl

end Atlas.Conway
