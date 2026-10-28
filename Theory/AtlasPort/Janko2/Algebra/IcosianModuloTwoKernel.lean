/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianModuloTwoKernel.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwo

/-!
# IcosianModuloTwoKernel

An integral icosian reduces to zero exactly when it is twice another
integral icosian. The inverse matrix coordinates reduce the assertion to
evenness of all golden-integer coefficients.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianModuloTwoKernel.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped QuadraticAlgebra
attribute [local irreducible] icosianIntegralCoefficients goldenModuloTwo

theorem goldenModuloTwo_eq_zero_iff_two_mul (x : GoldenInteger) :
    goldenModuloTwo x=0 ↔ ∃ y : GoldenInteger, x=2*y := by
  rw [goldenModuloTwo_eq_zero]
  constructor
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    refine ⟨⟨a,b⟩,?_⟩
    ext <;> simp [ha,hb]
  · rintro ⟨y,rfl⟩
    simp

theorem icosianModuloTwo_eq_zero_iff_coefficients (x : icosianOrder) :
    icosianModuloTwo x=0 ↔ icosianReducedCoefficients x=0 := by
  constructor
  · intro h
    have he := congrArg icosianMatrixCoefficients h
    change icosianMatrixCoefficients (icosianMatrixFromCoefficients _)=_ at he
    rw [icosianMatrixCoefficients_inverse] at he
    funext i
    have hi := congrFun he i
    fin_cases i <;> simpa [icosianMatrixCoefficients] using hi
  · intro h
    change icosianMatrixFromCoefficients _=0
    rw [h]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [icosianMatrixFromCoefficients]

theorem icosianModuloTwo_eq_zero_iff_two_mul (x : icosianOrder) :
    icosianModuloTwo x=0 ↔ ∃ y : icosianOrder, x=2*y := by
  rw [icosianModuloTwo_eq_zero_iff_coefficients]
  constructor
  · intro hx
    have he : ∀ i, ∃ y : GoldenInteger, icosianIntegralCoefficients x i=2*y := by
      intro i
      apply (goldenModuloTwo_eq_zero_iff_two_mul _).mp
      exact congrFun hx i
    choose a ha using he
    refine ⟨icosianIntegralSynthesis a,?_⟩
    apply icosianIntegralEquiv.injective
    have hy : icosianIntegralCoefficients (icosianIntegralSynthesis a)=a :=
      icosianIntegralEquiv.apply_symm_apply a
    change icosianIntegralCoefficients x=icosianIntegralCoefficients (2*icosianIntegralSynthesis a)
    have hdouble : 2*icosianIntegralSynthesis a=icosianIntegralSynthesis a+icosianIntegralSynthesis a :=
      two_mul _
    rw [hdouble]
    have hadd := icosianIntegralEquiv.map_add (icosianIntegralSynthesis a) (icosianIntegralSynthesis a)
    change icosianIntegralCoefficients (_+_)=
      icosianIntegralCoefficients (icosianIntegralSynthesis a)+
      icosianIntegralCoefficients (icosianIntegralSynthesis a) at hadd
    rw [hadd,hy]
    funext i
    simpa [two_mul] using ha i
  · rintro ⟨y,rfl⟩
    apply (icosianModuloTwo_eq_zero_iff_coefficients _).mp
    rw [map_mul,map_ofNat]
    have hz : (2 : IcosianMatrix)=0 := by
      rw [← one_add_one_eq_two]
      funext i j
      fin_cases i <;> fin_cases j <;> ext <;> norm_num [Matrix.one_apply] <;> decide
    rw [hz,zero_mul]

end Atlas.Algebra
