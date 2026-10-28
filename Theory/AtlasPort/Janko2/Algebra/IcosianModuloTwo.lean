/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianModuloTwo.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoMatrix
public import Theory.AtlasPort.Janko2.Algebra.IcosianIntegralMultiplication

/-!
# IcosianModuloTwo

Coefficient reduction defines a surjective ring homomorphism from
the integral icosian order to M₂(F₄). The explicit matrix presentation
proves multiplicativity and lifts every target matrix.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianModuloTwo.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix QuadraticAlgebra
attribute [local irreducible] icosianIntegralCoefficients goldenModuloTwo

def icosianReducedCoefficients (x : icosianOrder) : Fin 4 → GoldenFour :=
  fun i => goldenModuloTwo (icosianIntegralCoefficients x i)

theorem icosianReducedCoefficients_mul (x y : icosianOrder) :
    icosianReducedCoefficients (x*y)=icosianCoefficientProduct goldenFourTau
      (icosianReducedCoefficients x) (icosianReducedCoefficients y) := by
  funext i
  unfold icosianReducedCoefficients
  rw [icosianIntegralCoefficients_mul]
  have ht : goldenModuloTwo (QuadraticAlgebra.omega : GoldenInteger)=goldenFourTau := by
    unfold goldenModuloTwo goldenFourTau; rfl
  fin_cases i <;> simp [icosianCoefficientProduct,ht]

theorem icosianReducedCoefficients_add (x y : icosianOrder) :
    icosianReducedCoefficients (x+y)=icosianReducedCoefficients x+icosianReducedCoefficients y := by
  have he : icosianIntegralCoefficients (x+y)=icosianIntegralCoefficients x+
      icosianIntegralCoefficients y := icosianIntegralEquiv.map_add x y
  funext i
  simp [icosianReducedCoefficients,he]

def icosianModuloTwo : icosianOrder →+* IcosianMatrix where
  toFun x := icosianMatrixFromCoefficients (icosianReducedCoefficients x)
  map_one' := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [icosianMatrixFromCoefficients,icosianReducedCoefficients,
        icosianIntegralCoefficients_one]
  map_mul' x y := by
    rw [icosianReducedCoefficients_mul,icosianMatrixFromCoefficients_mul]
  map_zero' := by
    have he : icosianIntegralCoefficients (0 : icosianOrder)=0 := icosianIntegralEquiv.map_zero
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [icosianMatrixFromCoefficients,icosianReducedCoefficients,he]
  map_add' x y := by
    rw [icosianReducedCoefficients_add]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [icosianMatrixFromCoefficients,mul_add] <;> ring

theorem icosianModuloTwo_surjective : Function.Surjective icosianModuloTwo := by
  intro m
  choose a ha using (fun i => goldenModuloTwo_surjective (icosianMatrixCoefficients m i))
  refine ⟨icosianIntegralSynthesis a,?_⟩
  change icosianMatrixFromCoefficients (icosianReducedCoefficients _)=m
  have he : icosianReducedCoefficients (icosianIntegralSynthesis a)=icosianMatrixCoefficients m := by
    have hi : icosianIntegralCoefficients (icosianIntegralSynthesis a)=a :=
      icosianIntegralEquiv.apply_symm_apply a
    funext i
    simp [icosianReducedCoefficients,hi,ha]
  rw [he,icosianMatrixFromCoefficients_inverse]

end Atlas.Algebra
