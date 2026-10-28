/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRightLinearity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianScalarStructure

/-!
# Icosian Right Linearity

Commutation with the two icosian algebra generators forces full right
quaternionic linearity. Commuting scalars form a rational subalgebra,
so the generator theorem extends commutation to every scalar.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRightLinearity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Atlas.Lattices
open Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

/-- Scalars commuting with a rational-linear map form a rational subalgebra;
right multiplication reverses composition, but this still gives multiplicative closure. -/
def icosianCommutingScalars (f : Module.End ℚ IcosianRationalCoordinates) :
    Subalgebra ℚ IcosianQuaternion where
  carrier := {a | ∀ x, f (icosianRightMul x a)=icosianRightMul (f x) a}
  zero_mem' := by
    intro x
    have he (y : IcosianRationalCoordinates) : icosianRightMul y 0=0 := by
      funext j; exact mul_zero _
    rw [he,map_zero,he]
  one_mem' := by
    intro x
    have he (y : IcosianRationalCoordinates) : icosianRightMul y 1=y := by
      funext j; exact mul_one _
    rw [he,he]
  add_mem' := by
    intro a b ha hb x
    have he (y : IcosianRationalCoordinates) :
        icosianRightMul y (a+b)=icosianRightMul y a+icosianRightMul y b := by
      funext j; exact mul_add _ _ _
    rw [he,map_add,ha,hb,he]
  mul_mem' := by
    intro a b ha hb x
    have he (y : IcosianRationalCoordinates) :
        icosianRightMul y (a*b)=icosianRightMul (icosianRightMul y a) b := by
      funext j; exact (mul_assoc _ _ _).symm
    rw [he,hb,ha,he]
  algebraMap_mem' := by
    intro r x
    have he (y : IcosianRationalCoordinates) :
        icosianRightMul y (algebraMap ℚ IcosianQuaternion r)=r • y := by
      funext j
      simp [icosianRightMul,Algebra.algebraMap_eq_smul_one,Algebra.mul_smul_comm]
    rw [he,map_smul,he]

/-- Commutation with the two actual icosian generators forces full right-D linearity. -/
theorem icosian_right_linear_of_generators
    (f : Module.End ℚ IcosianRationalCoordinates)
    (hi : ∀ x,f (icosianRightMul x icosianI)=icosianRightMul (f x) icosianI)
    (hg : ∀ x,f (icosianRightMul x icosianGenerator)=icosianRightMul (f x) icosianGenerator) :
    ∀ a x,f (icosianRightMul x a)=icosianRightMul (f x) a := by
  let S := icosianCommutingScalars f
  have hI : icosianGeneratedOrder ≤ S.toSubring := by
    apply Subring.closure_le.mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact hi
    · exact hg
  have ht : (goldenTau : IcosianQuaternion) ∈ S := hI icosianTau_mem_generated
  have hk (a : GoldenRational) : (a : IcosianQuaternion) ∈ S := by
    have he : (a : IcosianQuaternion)=
        a.re • (1 : IcosianQuaternion)+a.im • (goldenTau : IcosianQuaternion) := by
      ext <;> simp [goldenTau,QuadraticAlgebra.omega]
    rw [he]
    exact S.add_mem (S.smul_mem S.one_mem a.re) (S.smul_mem ht a.im)
  have hb (a : GoldenRational) (b : IcosianQuaternion) (h : b ∈ S) : a • b ∈ S := by
    rw [← Quaternion.coe_mul_eq_smul]
    exact S.mul_mem (hk a) h
  intro a
  change a ∈ S
  rw [← icosianBasisSynthesis_coefficients a]
  unfold icosianBasisSynthesis
  exact S.add_mem (S.add_mem (S.add_mem (hb _ _ S.one_mem) (hb _ _ hi))
    (hb _ _ hg)) (hb _ _ (S.mul_mem hi hg))

end Atlas.Lattices
