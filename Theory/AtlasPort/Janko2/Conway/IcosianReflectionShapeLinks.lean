/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionShapeLinks.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionAxisNorm
public import Theory.AtlasPort.Janko2.Conway.IcosianRootLocalReferences
public import Theory.AtlasPort.Janko2.Conway.IcosianLineReflections
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisRootGeometry

/-!
# IcosianReflectionShapeLinks

Reflecting selected coordinate axes in explicit roots produces each local shape.
Computed coordinate norms certify the required connections.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionShapeLinks.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Quaternion Matrix QuadraticAlgebra

def icosianReflectedAxisRoot (r : IcosianRoot) (i : Fin 3) : IcosianRoot :=
  icosianRootReflectionOf r • icosianAxisRoot (i,1)

theorem icosianAxisRoot_embedding (i : Fin 3) :
    icosianCoordinateEmbedding (icosianAxisRoot (i,1)).val=Pi.single i 2 := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [icosianCoordinateEmbedding,icosianAxisRoot,icosianSingle,icosianUnitIntegral]
    rfl
  · simp [icosianCoordinateEmbedding,icosianAxisRoot,icosianSingle,hj]

theorem icosianReflectedAxisRoot_norm (r : IcosianRoot) (i j : Fin 3) :
    icosianNorm ((icosianReflectedAxisRoot r i).val j).val=
      if j=i then (2-icosianNorm (r.val i).val)^2
      else icosianNorm (r.val j).val*icosianNorm (r.val i).val := by
  have he := congrFun (icosianHermitianRoot_embedding (icosianRootReflectionOf r) (icosianAxisRoot (i,1))) j
  rw [icosianAxisRoot_embedding,icosianRootReflectionOf_apply] at he
  change ((icosianReflectedAxisRoot r i).val j).val=_ at he
  rw [he,icosianReflection_axis_norm]
  rfl

theorem icosianReflectedAxisRoot_norm_word (r : IcosianRoot) (i j : Fin 3) :
    icosianRootNormWord (icosianReflectedAxisRoot r i) j=
      if j=i then (2-icosianRootNormWord r i)^2
      else icosianRootNormWord r j*icosianRootNormWord r i := by
  apply goldenIntegerToRational_injective
  simp only [icosianRootNormWord,icosianIntegralNorm_spec,apply_ite,map_pow,map_sub,map_mul,map_ofNat]
  simpa only [apply_ite] using icosianReflectedAxisRoot_norm r i j

theorem icosianLocalCRoot_norm_word : icosianRootNormWord icosianLocalCRoot=![2,1,1] := by
  funext j
  apply icosianRootNormWord_of_norm
  fin_cases j
  · exact icosianLocalCScalar_norm
  · exact icosianNormOneGroup_norm 1
  · exact icosianNormOneGroup_norm 1

theorem icosianReflection_C_axis0_shape : HasIcosianRootShape (icosianReflectedAxisRoot icosianLocalCRoot 0) 1 := by
  have hw : icosianRootNormWord (icosianReflectedAxisRoot icosianLocalCRoot 0)=![0,2,2] := by
    funext j
    rw [icosianReflectedAxisRoot_norm_word,icosianLocalCRoot_norm_word]
    fin_cases j <;> decide +kernel
  change List.Perm _ [0,2,2]
  rw [hw]
  decide +kernel

theorem icosianReflection_C_axis1_shape : HasIcosianRootShape (icosianReflectedAxisRoot icosianLocalCRoot 1) 2 := by
  have hw : icosianRootNormWord (icosianReflectedAxisRoot icosianLocalCRoot 1)=![2,1,1] := by
    funext j
    rw [icosianReflectedAxisRoot_norm_word,icosianLocalCRoot_norm_word]
    fin_cases j <;> decide +kernel
  change List.Perm _ [1,1,2]
  rw [hw]
  decide +kernel

theorem icosianReflection_D_axis2_shape : HasIcosianRootShape (icosianReflectedAxisRoot icosianLocalDRoot 2) 3 := by
  have hw : icosianRootNormWord (icosianReflectedAxisRoot icosianLocalDRoot 2)=![(1-ω)^2,ω^2,1] := by
    funext j
    rw [icosianReflectedAxisRoot_norm_word,icosianLocalDRoot_norm_word]
    fin_cases j <;> decide +kernel
  change List.Perm _ [1,ω^2,(1-ω)^2]
  rw [hw]
  decide +kernel

theorem icosianReflectedAxisRoot_point (r : IcosianRoot) (i : Fin 3) :
    icosianRootToPoint (icosianReflectedAxisRoot r i)=icosianRootReflectionOf r • icosianRootAxisPoint i :=
  icosianRootToPoint_smul _ _

end Atlas.Conway
