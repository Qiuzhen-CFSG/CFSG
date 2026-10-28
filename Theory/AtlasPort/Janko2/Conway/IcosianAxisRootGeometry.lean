/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisRootGeometry.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointOrthogonality
public import Theory.AtlasPort.Janko2.Lattices.IcosianZeroRoots
public import Theory.AtlasPort.Janko2.Algebra.IcosianOrthogonalPair

/-!
# IcosianAxisRootGeometry

Coordinate roots define three distinct projective root points. Evaluating the
Hermitian form characterizes orthogonality to each coordinate axis.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisRootGeometry.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Quaternion BigOperators

def icosianRootAxisPoint (i : Fin 3) : IcosianRootPoint :=
  icosianRootToPoint (icosianAxisRoot (i,1))

theorem icosianRootAxisPoint_val (i : Fin 3) :
    (icosianRootAxisPoint i).val=icosianAxisPoint i := by
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨MulOpposite.op (2 : IcosianQuaternion),?_⟩
  funext j
  by_cases hj : j=i
  · subst j
    simp [icosianAxisRoot,icosianSingle,icosianCoordinateEmbedding,icosianUnitIntegral]
    rfl
  · simp [icosianAxisRoot,icosianSingle,icosianCoordinateEmbedding,hj]

theorem icosianRootAxisPoint_injective : Function.Injective icosianRootAxisPoint := by
  intro i j h
  apply icosianAxisPoint_injective
  simpa only [icosianRootAxisPoint_val] using congrArg Subtype.val h

theorem icosianAxisRoot_hermitian (i : Fin 3) (x : IcosianRationalCoordinates) :
    icosianHermitian (icosianCoordinateEmbedding (icosianAxisRoot (i,1)).val) x=x i := by
  fin_cases i <;>
    simp [icosianHermitian,icosianCoordinateEmbedding,icosianAxisRoot,icosianSingle,
      icosianUnitIntegral,Fin.sum_univ_succ]
  all_goals change (2 : ℚ)⁻¹ • (star (2 : IcosianQuaternion)*_)=_
  all_goals simp only [star_ofNat,two_mul,smul_add,← add_smul]
  all_goals norm_num

theorem icosianRootAxisPoint_orthogonal_iff (i : Fin 3) (r : IcosianRoot) :
    IcosianRootPointOrthogonal (icosianRootAxisPoint i) (icosianRootToPoint r) ↔ r.val i=0 := by
  change IcosianRootPointOrthogonal (icosianRootToPoint (icosianAxisRoot (i,1))) (icosianRootToPoint r) ↔ _
  rw [icosianRootPointOrthogonal_iff,icosianAxisRoot_hermitian]
  change (r.val i).val=(0 : icosianOrder).val ↔ r.val i=0
  exact Subtype.val_inj

end Atlas.Conway
