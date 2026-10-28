/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianGlueFreeCoordinates.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianCongruence
public import Theory.AtlasPort.Janko2.Codes.IcosianMatrixGlue

/-!
# Icosian Glue Free Coordinates

Reduction identifies the icosian congruences with the matrix glue.
Six free coefficients determine a glue word uniquely; a coordinate
calculation proves that a word with zero free part vanishes.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianGlueFreeCoordinates.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix QuadraticAlgebra

/-- The actual ideal congruences are exactly the two-column matrix glue. -/
theorem icosianLeechModule_matrix_glue (x : IcosianCoordinates) :
    x ∈ icosianLeechModule ↔
      (fun i => icosianModuloTwo (x i)) ∈ icosianMatrixGlue GoldenFour := by
  rw [icosianLeechModule_mem,icosianP_mem,icosianP_mem,icosianPZero_mem,
    icosianMatrixGlue_constraints]
  simp only [map_sub,map_add,Matrix.sub_apply,Matrix.add_apply,sub_eq_zero]
  constructor
  · rintro ⟨h1,h2,h0⟩ j
    exact ⟨(h1 j).symm,(h1 j).trans (h2 j).symm,h0 j⟩
  · intro h
    exact ⟨fun j => (h j).1.symm,
      fun j => ((h j).1.trans (h j).2.1).symm,fun j => (h j).2.2⟩

/-- Six free field coefficients determine a glue vector: the second block's
coefficients numbered 1 and 3, and every coefficient of the third block. -/
theorem icosianGlue_free_zero (a : Fin 3 → Fin 4 → GoldenFour)
    (ha : (fun i => icosianMatrixFromCoefficients (a i)) ∈ icosianMatrixGlue GoldenFour)
    (h1 : a 1 1=0) (h3 : a 1 3=0) (h2 : a 2=0) : a=0 := by
  have hh := (icosianMatrixGlue_constraints _).mp ha
  have ht : goldenFourTau ≠ 0 := by
    intro h
    have := congrArg QuadraticAlgebra.im h
    norm_num [goldenFourTau,QuadraticAlgebra.omega] at this
  have h12 : a 1 2=0 := by
    have h := (hh 0).2.1
    simp [icosianMatrixFromCoefficients,h2,h3] at h
    exact h.resolve_left ht
  have h10 : a 1 0=0 := by
    have h := (hh 1).2.1
    simpa [icosianMatrixFromCoefficients,h2,h1,h3,h12] using h
  have hb : a 1=0 := by
    funext j
    fin_cases j <;> simp [h10,h1,h12,h3]
  have hm : icosianMatrixFromCoefficients (a 0)=0 := by
    funext r j
    fin_cases r
    · have h := (hh j).2.2
      fin_cases j <;>
      simpa [hb,h2,icosianMatrixFromCoefficients] using h
    · have h := (hh j).1
      fin_cases j <;>
      simpa [hb,icosianMatrixFromCoefficients] using h
  have h0 : a 0=0 := by
    rw [← icosianMatrixCoefficients_inverse (a 0),hm]
    simp [icosianMatrixCoefficients]
  funext i
  fin_cases i <;> assumption

end Atlas.Lattices
