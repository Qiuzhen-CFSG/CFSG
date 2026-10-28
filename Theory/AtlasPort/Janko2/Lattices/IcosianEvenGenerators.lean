/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianEvenGenerators.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonGeneratorsData
public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoKernel

/-!
# Icosian Even Generators

The first 24 source generators span all integral coordinates whose
coefficients reduce to zero modulo two. Halving the integral coefficients
expresses each such vector as a sum of doubled basis vectors.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianEvenGenerators.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators QuadraticAlgebra
attribute [local irreducible] icosianIntegralCoefficients icosianIntegralSynthesis

theorem icosianSourceGenerator_coefficients (n : Fin 36) (i : Fin 3) :
    icosianIntegralLinearEquiv (icosianComparisonSourceGenerator n i)=
      icosianComparisonSourceCoefficients n i :=
  icosianIntegralEquiv.apply_symm_apply _

theorem icosianEven_mem_of_generators (S : Submodule ℤ IcosianCoordinates)
    (hS : ∀ n : Fin 24,icosianComparisonSourceGenerator ⟨n.val,by omega⟩ ∈ S)
    (x : IcosianCoordinates)
    (hx : ∀ i j,goldenModuloTwo (icosianIntegralCoefficients (x i) j)=0) : x ∈ S := by
  let c : IcosianRealIndex → ℤ := fun p =>
    if p.2.2=0 then (icosianIntegralCoefficients (x p.1) p.2.1).re/2
    else (icosianIntegralCoefficients (x p.1) p.2.1).im/2
  let g : IcosianRealIndex → IcosianCoordinates := fun p =>
    icosianComparisonSourceGenerator ⟨(icosianRealCoordinateIndex p).val,by
      have := (icosianRealCoordinateIndex p).isLt; omega⟩
  have he : (∑ p,c p • g p)=x := by
    funext i
    apply icosianIntegralLinearEquiv.injective
    simp only [Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]
    funext j
    have hr := Int.ediv_mul_cancel ((goldenModuloTwo_eq_zero _).mp (hx i j)).1
    have hi := Int.ediv_mul_cancel ((goldenModuloTwo_eq_zero _).mp (hx i j)).2
    simp only [g,icosianSourceGenerator_coefficients]
    fin_cases i <;> fin_cases j <;> ext <;>
      simp [c,icosianComparisonSourceCoefficients,icosianComparisonSourceData,
        icosianRealCoordinateIndex,Fintype.sum_prod_type,Fin.sum_univ_succ] <;>
      first | exact hr | exact hi
  rw [← he]
  exact S.sum_mem fun p _ => S.smul_mem (c p) (hS (icosianRealCoordinateIndex p))

end Atlas.Lattices
