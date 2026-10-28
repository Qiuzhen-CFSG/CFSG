/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRootNormShapes.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRootNormConstraints
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormTripleArithmetic

/-!
# Icosian Root Norm Shapes

Coordinate norms of actual Hermitian norm-two roots have one of the
four specified shapes. Positivity, the exact norm sum, and the even-norm
constraint for zero coordinates discharge the arithmetic classification.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRootNormShapes.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra
open scoped QuadraticAlgebra Matrix BigOperators

/-- Exhaustive coordinate norm shapes for the actual quaternionic roots of
Hermitian norm two. No root enumeration or target cardinality is used. -/
theorem icosianRoot_norm_shapes (x : IcosianCoordinates)
    (hx : x∈icosianLeechModule)
    (hn : icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding x)=2) :
    IcosianRootNormShape (fun i => icosianIntegralNorm (x i)) := by
  let n := fun i => icosianIntegralNorm (x i)
  have hs := icosianRoot_integral_norm_sum x hn
  have hr : (n 0).re+(n 1).re+(n 2).re=4 := by
    simpa [n,Fin.sum_univ_succ,add_assoc] using congrArg QuadraticAlgebra.re hs
  have hi : (n 0).im+(n 1).im+(n 2).im=0 := by
    simpa [n,Fin.sum_univ_succ,add_assoc] using congrArg QuadraticAlgebra.im hs
  have hz : (n 0).re=0 ∨ (n 1).re=0 ∨ (n 2).re=0 →
      2∣(n 0).re ∧ 2∣(n 0).im ∧ 2∣(n 1).re ∧ 2∣(n 1).im ∧
      2∣(n 2).re ∧ 2∣(n 2).im := by
    intro h
    have he : ∃ i,x i=0 := by
      rcases h with h | h | h
      · exact ⟨0,(icosianIntegralNorm_real_zero (x 0)).mp h⟩
      · exact ⟨1,(icosianIntegralNorm_real_zero (x 1)).mp h⟩
      · exact ⟨2,(icosianIntegralNorm_real_zero (x 2)).mp h⟩
    obtain ⟨i,hi⟩ := he
    have h0 := icosianLeechModule_zero_even_norms x hx i hi 0
    have h1 := icosianLeechModule_zero_even_norms x hx i hi 1
    have h2 := icosianLeechModule_zero_even_norms x hx i hi 2
    exact ⟨h0.1,h0.2,h1.1,h1.2,h2.1,h2.2⟩
  have h := icosianNorm_triple_arithmetic (n 0).re (n 0).im (n 1).re (n 1).im
    (n 2).re (n 2).im (icosianIntegralNorm_real_nonneg (x 0))
    (icosianIntegralNorm_real_nonneg (x 1)) (icosianIntegralNorm_real_nonneg (x 2))
    (icosianIntegralNorm_discriminant_nonneg (x 0))
    (icosianIntegralNorm_discriminant_nonneg (x 1))
    (icosianIntegralNorm_discriminant_nonneg (x 2)) hr hi hz
  have he : ![⟨(n 0).re,(n 0).im⟩,⟨(n 1).re,(n 1).im⟩,
      ⟨(n 2).re,(n 2).im⟩]=(n : Fin 3 → GoldenInteger) := by
    funext i
    fin_cases i <;> rfl
  rwa [he] at h

end Atlas.Lattices
