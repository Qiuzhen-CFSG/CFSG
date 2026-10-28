/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianHermitianIntegral.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianGlueFreeCoordinates
public import Theory.AtlasPort.Janko2.Codes.IcosianMatrixGluePairing
public import Theory.AtlasPort.Janko2.Algebra.IcosianReductionConjugation
public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoKernel
public import Theory.AtlasPort.Janko2.Lattices.IcosianReflection

/-!
# Icosian Hermitian Integral

Pairings of integral lattice vectors lie in the icosian order. The matrix
glue pairing makes the integral sum divisible by two, and this integrality
proves that root reflections preserve the actual lattice.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianHermitianIntegral.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators Quaternion

theorem icosianHermitian_integral_coordinates (x y : IcosianCoordinates)
    (hx : x ∈ icosianLeechModule) (hy : y ∈ icosianLeechModule) :
    IsIcosian (icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding y)) := by
  let z : icosianOrder := ∑ i,icosianOrderStar (x i)*y i
  have hz : icosianModuloTwo z=0 := by
    simp only [z,map_sum,map_mul,icosianModuloTwo_star]
    exact icosianMatrixGlue_adjugate_pairing _ _
      ((icosianLeechModule_matrix_glue x).mp hx)
      ((icosianLeechModule_matrix_glue y).mp hy)
  obtain ⟨a,ha⟩ := (icosianModuloTwo_eq_zero_iff_two_mul z).mp hz
  have hval : (z : IcosianQuaternion)=(2 : ℚ) • a.val := by
    have h := congrArg Subtype.val ha
    rw [two_smul ℚ a.val]
    simpa [two_mul] using h
  have he : icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding y)=a.val := by
    change (1/2 : ℚ) • (z : IcosianQuaternion)=a.val
    rw [hval,smul_smul]
    norm_num
  rw [he]
  exact a.property

theorem icosianHermitian_integral {x y : IcosianRationalCoordinates}
    (hx : x ∈ rationalIcosianLattice) (hy : y ∈ rationalIcosianLattice) :
    IsIcosian (icosianHermitian x y) := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  exact icosianHermitian_integral_coordinates a b ha hb

/-- Lattice preservation comes from integral Hermitian pairings and the actual right module. -/
theorem icosianReflection_lattice {r v : IcosianRationalCoordinates}
    (hr : r ∈ rationalIcosianLattice) (hv : v ∈ rationalIcosianLattice) :
    icosianReflection r v ∈ rationalIcosianLattice := by
  let a : icosianOrder := ⟨icosianHermitian r v,icosianHermitian_integral hr hv⟩
  obtain ⟨rr,hrr,hre⟩ := hr
  obtain ⟨vv,hvv,hve⟩ := hv
  refine ⟨vv-MulOpposite.op a • rr,
    icosianLeechModule.sub_mem hvv (icosianLeechModule.smul_mem (MulOpposite.op a) hrr),?_⟩
  change icosianCoordinateEmbedding (vv-MulOpposite.op a • rr)=v-icosianRightMul r a.val
  rw [← hre,← hve]
  rfl

end Atlas.Lattices
