/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisNormInvariant.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointNormWord
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisRootGeometry
public import Theory.AtlasPort.Janko2.Lattices.IcosianHermitianIdentities

/-!
# IcosianAxisNormInvariant

The full stabilizer of a coordinate root line preserves its coordinate norm.
Hermitian invariance transfers the root calculation to projective points.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisNormInvariant.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Every element of the full line stabilizer preserves the coordinate norm
at that axis. This uses the actual quaternionic Hermitian form and the proved
unit saturation of root lines. -/
theorem icosianAxisStabilizer_root_norm (g : icosianHermitianGroup)
    (hg : g • icosianRootAxisPoint 0=icosianRootAxisPoint 0) (r : IcosianRoot) :
    icosianRootNormWord (g • r) 0=icosianRootNormWord r 0 := by
  let a : IcosianRoot := icosianAxisRoot (0,1)
  have hp : icosianRootPoint (g • a)=icosianRootPoint a := by
    rw [icosianRootPoint_smul]
    exact congrArg Subtype.val hg
  obtain ⟨u,hu⟩ := (icosianRootPoint_eq_iff a (g • a)).mp hp
  have hh : icosianHermitian (icosianCoordinateEmbedding (g • a).val)
      (icosianCoordinateEmbedding (g • r).val)=
      icosianHermitian (icosianCoordinateEmbedding a.val) (icosianCoordinateEmbedding r.val) := by
    change icosianHermitian (icosianCoordinateEmbedding (icosianHermitianRoot g a).val)
      (icosianCoordinateEmbedding (icosianHermitianRoot g r).val)=_
    rw [icosianHermitianRoot_embedding,icosianHermitianRoot_embedding,g.property.2.1]
  rw [hu] at hh
  change icosianHermitian (icosianRightMul (icosianCoordinateEmbedding a.val) u.val.val)
      (icosianCoordinateEmbedding (g • r).val)=
      icosianHermitian (icosianCoordinateEmbedding a.val) (icosianCoordinateEmbedding r.val) at hh
  rw [icosianHermitian_rightMul_left,icosianAxisRoot_hermitian,
    icosianAxisRoot_hermitian] at hh
  apply goldenIntegerToRational_injective
  simp only [icosianRootNormWord,icosianIntegralNorm_spec]
  have hn := congrArg icosianNorm hh
  rw [icosianNorm_mul,show icosianNorm (star u.val.val)=1 from
    (Quaternion.normSq_star _).trans (icosianNormOneGroup_norm u),one_mul] at hn
  exact hn

theorem icosianAxisStabilizer_point_norm (g : icosianHermitianGroup)
    (hg : g • icosianRootAxisPoint 0=icosianRootAxisPoint 0) (p : IcosianRootPoint) :
    icosianRootPointNormWord (g • p) 0=icosianRootPointNormWord p 0 := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  rw [← icosianRootToPoint_smul]
  simp only [icosianRootPointNormWord_toPoint]
  exact icosianAxisStabilizer_root_norm g hg r

end Atlas.Conway
