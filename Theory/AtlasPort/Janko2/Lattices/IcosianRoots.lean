/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRoots.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRootNormShapes
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneCard

/-!
# Icosian Roots

Roots are actual integral congruence vectors of quaternionic Hermitian
norm two. Single-coordinate calculations characterize axis membership
and show that the sole nonzero coordinate has norm four.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRoots.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Quaternion QuadraticAlgebra BigOperators

/-- The actual quaternionic roots: integral congruence vectors of Hermitian norm two. -/
def IcosianRoot := {x : IcosianCoordinates // x∈icosianLeechModule ∧
  icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding x)=2}

def icosianSingle (i : Fin 3) (z : icosianOrder) : IcosianCoordinates :=
  fun j => if j=i then z else 0

theorem icosianSingle_mem (i : Fin 3) (z : icosianOrder) :
    icosianSingle i z∈icosianLeechModule ↔ icosianModuloTwo z=0 := by
  rw [icosianLeechModule_matrix_glue,icosianMatrixGlue_constraints]
  fin_cases i <;> constructor
  all_goals
    first
    | (intro h; funext r j; fin_cases r
       · simpa [icosianSingle] using (h j).2.2
       · first
         | simpa [icosianSingle] using (h j).1
         | simpa [icosianSingle] using (h j).1.symm
         | simpa [icosianSingle] using (h j).2.1.symm)
    | (intro h j; simp [icosianSingle,h])

theorem icosianSingle_norm (i : Fin 3) (z : icosianOrder) :
    icosianHermitian (icosianCoordinateEmbedding (icosianSingle i z))
      (icosianCoordinateEmbedding (icosianSingle i z))=
      (1/2 : ℚ) • (icosianNorm z.val : IcosianQuaternion) := by
  fin_cases i <;> simp [icosianHermitian,icosianCoordinateEmbedding,icosianSingle,
    Fin.sum_univ_succ,Quaternion.star_mul_self,icosianNorm]

theorem icosianNorm_double (z : IcosianQuaternion) :
    icosianNorm (2*z)=4*icosianNorm z := by
  rw [icosianNorm_mul]
  have h : icosianNorm (2 : IcosianQuaternion)=(4 : GoldenRational) := by
    ext <;> norm_num [icosianNorm_coordinates,QuaternionAlgebra.re_ofNat,QuaternionAlgebra.imI_ofNat,QuaternionAlgebra.imJ_ofNat,QuaternionAlgebra.imK_ofNat]
  rw [h]

theorem icosianRoot_single_norm (r : IcosianRoot) (i : Fin 3)
    (h : ∀ j,j≠i → r.val j=0) : icosianNorm (r.val i).val=4 := by
  have he : r.val=icosianSingle i (r.val i) := by
    funext j
    by_cases hj : j=i
    · simp [icosianSingle,hj]
    · simp [icosianSingle,hj,h j hj]
  have hn := r.property.2
  rw [he,icosianSingle_norm] at hn
  have hc := congrArg (fun z : IcosianQuaternion => z.re) hn
  change (1/2 : ℚ) • icosianNorm (r.val i).val=2 at hc
  calc
    icosianNorm (r.val i).val=(2 : ℚ) • ((1/2 : ℚ) • icosianNorm (r.val i).val) := by
      simp [smul_smul]
    _=(2 : ℚ) • (2 : GoldenRational) := by rw [hc]
    _=4 := by ext <;> norm_num

end Atlas.Lattices
