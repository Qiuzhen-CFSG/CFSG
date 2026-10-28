/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinRank.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinRational
public import Theory.AtlasPort.OtherSporadic.Algebra.QuadraticIndex
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Eisenstein Rank

The congruence lattice has integral rank 24. Containment of coordinate multiples and the rational embedding compare its rank with the ambient lattice.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinRank.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Lattices
open Atlas.Algebra
open scoped QuadraticAlgebra

instance eisensteinLeech_free : Module.Free ℤ eisensteinLeechModule :=
  inferInstanceAs (Module.Free ℤ (eisensteinLeechModule.restrictScalars ℤ))

instance eisensteinLeech_finite : Module.Finite ℤ eisensteinLeechModule :=
  inferInstanceAs (Module.Finite ℤ (eisensteinLeechModule.restrictScalars ℤ))

def eisensteinNineIntoLattice : EisensteinCoordinates →ₗ[ℤ] eisensteinLeechModule where
  toFun z := ⟨(9 : Eisenstein) • z, eisensteinLeechModule_contains_nine z⟩
  map_add' z w := by apply Subtype.ext; exact smul_add _ _ _
  map_smul' r z := by apply Subtype.ext; exact smul_comm _ _ _

theorem eisensteinNineIntoLattice_injective :
    Function.Injective eisensteinNineIntoLattice := by
  intro z w h
  have he := congrArg Subtype.val h
  funext i
  have hi := congrFun he i
  have hr := congrArg QuadraticAlgebra.re hi
  have hs := congrArg QuadraticAlgebra.im hi
  simp [eisensteinNineIntoLattice, Pi.smul_apply, smul_eq_mul] at hr hs
  ext <;> omega

theorem eisensteinLeech_rank : Module.finrank ℤ eisensteinLeechModule = 24 := by
  have h₁ := LinearMap.finrank_le_finrank_of_injective
    (eisensteinLeechModule.restrictScalars ℤ).subtype_injective
  change Module.finrank ℤ eisensteinLeechModule ≤ Module.finrank ℤ EisensteinCoordinates at h₁
  have h₂ := LinearMap.finrank_le_finrank_of_injective eisensteinNineIntoLattice_injective
  have h : Module.finrank ℤ EisensteinCoordinates = 24 := by
    simp [EisensteinCoordinates, Eisenstein, Module.finrank_pi_fintype,
      QuadraticAlgebra.finrank_eq_two]
  rw [h] at h₁ h₂
  omega

def eisensteinThetaEnd : Module.End ℤ eisensteinLeechModule where
  toFun z := eisensteinTheta • z
  map_add' z w := smul_add eisensteinTheta z w
  map_smul' r z := smul_comm eisensteinTheta r z

theorem eisensteinThetaEnd_square :
    eisensteinThetaEnd * eisensteinThetaEnd =
      (-3 : ℤ) • (1 : Module.End ℤ eisensteinLeechModule) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  funext i
  change eisensteinTheta * (eisensteinTheta * z.val i) = (-3 : ℤ) • z.val i
  rw [← mul_assoc, ← pow_two, eisensteinTheta_sq]
  simp

theorem eisensteinThetaEnd_injective : Function.Injective eisensteinThetaEnd := by
  intro z w h
  have hh := congrArg eisensteinThetaEnd h
  have he := LinearMap.congr_fun eisensteinThetaEnd_square z
  have hw := LinearMap.congr_fun eisensteinThetaEnd_square w
  change eisensteinThetaEnd (eisensteinThetaEnd z) = (-3 : ℤ) • z at he
  change eisensteinThetaEnd (eisensteinThetaEnd w) = (-3 : ℤ) • w at hw
  rw [he, hw] at hh
  have hv := congrArg Subtype.val hh
  apply Subtype.ext
  funext i
  have hi := congrFun hv i
  have hr := congrArg QuadraticAlgebra.re hi
  have hs := congrArg QuadraticAlgebra.im hi
  simp at hr hs
  ext <;> omega

theorem eisensteinTheta_quotient_card :
    Nat.card (eisensteinLeechModule ⧸ eisensteinThetaEnd.range) = 3^12 := by
  apply card_quotient_range_of_square_neg eisensteinThetaEnd eisensteinThetaEnd_injective 3 12
  · exact eisensteinLeech_rank
  · exact eisensteinThetaEnd_square

end Atlas.Lattices
