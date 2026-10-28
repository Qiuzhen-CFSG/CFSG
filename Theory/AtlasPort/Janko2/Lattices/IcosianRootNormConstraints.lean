/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRootNormConstraints.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianGlueFreeCoordinates
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormDiscriminant
public import Theory.AtlasPort.Janko2.Algebra.IcosianReductionNorm

/-!
# Icosian Root Norm Constraints

A zero coordinate forces every reduction into the common row ideal
and every coordinate norm to be even. The Hermitian norm-two equation
also gives the exact integral golden norm sum four.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRootNormConstraints.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators Quaternion QuadraticAlgebra

/-- A zero block forces all three reductions into the rank-one row ideal. -/
theorem icosianLeechModule_zero_row (x : IcosianCoordinates)
    (hx : x∈icosianLeechModule) (i : Fin 3) (hi : x i=0) :
    ∀ k j,icosianModuloTwo (x k) 1 j=0 := by
  have h := (icosianMatrixGlue_constraints _).mp
    ((icosianLeechModule_matrix_glue x).mp hx)
  intro k j
  have hz : icosianModuloTwo (x i) 1 j=0 := by rw [hi,map_zero]; rfl
  have h01 := (h j).1
  have h12 := (h j).2.1
  fin_cases i <;> fin_cases k <;> simp_all

theorem icosianLeechModule_zero_even_norms (x : IcosianCoordinates)
    (hx : x∈icosianLeechModule) (i : Fin 3) (hi : x i=0) (k : Fin 3) :
    2∣(icosianIntegralNorm (x k)).re ∧ 2∣(icosianIntegralNorm (x k)).im := by
  apply (goldenModuloTwo_eq_zero _).mp
  rw [← icosianModuloTwo_det,Matrix.det_fin_two]
  simp [icosianLeechModule_zero_row x hx i hi k]

/-- The quaternionic root norm is equivalent to the exact integral golden
norm sum four, not merely a rational trace condition. -/
theorem icosianRoot_integral_norm_sum (x : IcosianCoordinates)
    (hx : icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding x)=2) :
    (∑ i,icosianIntegralNorm (x i))=4 := by
  apply goldenIntegerToRational_injective
  have hs : (∑ i,icosianNorm (x i).val)=4 := by
    have h := congrArg (fun z : IcosianQuaternion => z.re) hx
    have hg : (1/2 : ℚ) • (∑ i,icosianNorm (x i).val)=(2 : GoldenRational) := by
      simpa [icosianHermitian,icosianCoordinateEmbedding,Quaternion.star_mul_self,
        Fin.sum_univ_succ,icosianNorm,QuaternionAlgebra.re_ofNat] using h
    calc
      (∑ i,icosianNorm (x i).val) = (2 : ℚ) • ((1/2 : ℚ) •
          (∑ i,icosianNorm (x i).val)) := by simp [smul_smul]
      _ = (2 : ℚ) • (2 : GoldenRational) := by rw [hg]
      _ = 4 := by ext <;> norm_num
  simpa only [map_sum,icosianIntegralNorm_spec,map_ofNat] using hs

end Atlas.Lattices
