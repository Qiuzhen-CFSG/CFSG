/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/GoldenModuloTwo.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianIntegralCoordinates
public import Mathlib.Data.ZMod.Basic

/-!
# GoldenModuloTwo

Reduction of golden integers modulo two gives the quadratic field F₄.
Coefficient reduction proves surjectivity and characterizes the kernel by
even real and golden coefficients.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/GoldenModuloTwo.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Algebra
open scoped QuadraticAlgebra

abbrev GoldenFour := QuadraticAlgebra (ZMod 2) 1 1

instance goldenFour_irreducible : Fact (∀ r : ZMod 2, r^2≠1+1*r) := ⟨by decide⟩

def goldenFourTau : GoldenFour := QuadraticAlgebra.omega

def goldenModuloTwo : GoldenInteger →+* GoldenFour where
  toFun z := ⟨z.re,z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' := by intros; ext <;> simp
  map_mul' := by intros; ext <;> simp

theorem goldenModuloTwo_surjective : Function.Surjective goldenModuloTwo := by
  intro x
  refine ⟨⟨x.re.val,x.im.val⟩,?_⟩
  ext <;> simp [goldenModuloTwo]

theorem goldenModuloTwo_eq_zero (x : GoldenInteger) :
    goldenModuloTwo x=0 ↔ 2∣x.re ∧ 2∣x.im := by
  rw [QuadraticAlgebra.ext_iff]
  simp [goldenModuloTwo, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem goldenFourTau_sq : goldenFourTau^2=1+goldenFourTau := by
  ext <;> norm_num [goldenFourTau,QuadraticAlgebra.omega,pow_two]

end Atlas.Algebra
