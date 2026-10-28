/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisReflections.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLineReflections
public import Theory.AtlasPort.Janko2.Lattices.IcosianAxisRoots

/-!
# IcosianAxisReflections

Coordinate root reflections give commuting sign changes. Their product is the central
negation, whose square and commutation relations are proved pointwise.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisReflections.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped BigOperators Quaternion

def icosianAxisReflection (i : Fin 3) : icosianHermitianGroup :=
  icosianRootReflectionOf (icosianAxisRoot (i,1))

theorem icosianHermitian_axis_two (i : Fin 3) (v : IcosianRationalCoordinates) :
    icosianHermitian (Pi.single i (2 : IcosianQuaternion) : IcosianRationalCoordinates) v=v i := by
  have he : (∑ j : Fin 3,star ((Pi.single i (2 : IcosianQuaternion) : IcosianRationalCoordinates) j)*v j)=2*v i := by
    fin_cases i <;> simp [Fin.sum_univ_succ]
  change (1/2 : ℚ) • (∑ j : Fin 3,star ((Pi.single i (2 : IcosianQuaternion) : IcosianRationalCoordinates) j)*v j)=_
  rw [he,two_mul,smul_add,← add_smul]
  norm_num

theorem icosianAxisReflection_apply (i j : Fin 3) (v : IcosianRationalCoordinates) :
    (icosianAxisReflection i).val v j=if j=i then -v j else v j := by
  have he : icosianCoordinateEmbedding (icosianAxisRoot (i,1)).val=Pi.single i 2 := by
    funext k
    by_cases hk : k=i <;>
      simp [icosianCoordinateEmbedding,icosianAxisRoot,icosianSingle,icosianUnitIntegral,hk]
    rfl
  change icosianReflection (icosianCoordinateEmbedding (icosianAxisRoot (i,1)).val) v j=_
  rw [he]
  simp only [icosianReflection,icosianHermitian_axis_two,Pi.sub_apply,icosianRightMul]
  by_cases hj : j=i <;> simp [hj,two_mul]

theorem icosianAxisReflection_mem (i : Fin 3) :
    icosianAxisReflection i∈icosianReflectionGroup :=
  icosianRootReflectionOf_mem _

theorem icosianAxisReflection_mul_comm (i j : Fin 3) :
    icosianAxisReflection i*icosianAxisReflection j=
      icosianAxisReflection j*icosianAxisReflection i := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  funext k
  change (icosianAxisReflection i).val ((icosianAxisReflection j).val v) k=
    (icosianAxisReflection j).val ((icosianAxisReflection i).val v) k
  simp only [icosianAxisReflection_apply]
  split_ifs <;> simp

def icosianCentralSign : icosianHermitianGroup :=
  icosianAxisReflection 0*icosianAxisReflection 1*icosianAxisReflection 2

theorem icosianCentralSign_apply (v : IcosianRationalCoordinates) :
    icosianCentralSign.val v= -v := by
  funext i
  change (icosianAxisReflection 0).val
    ((icosianAxisReflection 1).val ((icosianAxisReflection 2).val v)) i=_
  simp only [icosianAxisReflection_apply]
  fin_cases i <;> simp

theorem icosianCentralSign_mem_reflectionGroup :
    icosianCentralSign∈icosianReflectionGroup :=
  icosianReflectionGroup.mul_mem
    (icosianReflectionGroup.mul_mem (icosianAxisReflection_mem 0) (icosianAxisReflection_mem 1))
    (icosianAxisReflection_mem 2)

theorem icosianCentralSign_square : icosianCentralSign*icosianCentralSign=1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change icosianCentralSign.val (icosianCentralSign.val v)=v
  simp only [icosianCentralSign_apply,neg_neg]

theorem icosianCentralSign_comm (g : icosianHermitianGroup) :
    icosianCentralSign*g=g*icosianCentralSign := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change icosianCentralSign.val (g.val v)=g.val (icosianCentralSign.val v)
  simp only [icosianCentralSign_apply,map_neg]

end Atlas.Conway
