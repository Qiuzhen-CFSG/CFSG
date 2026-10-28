/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Siegel transformations are products of reflections in dimension at least five

Adapted from `Atlas/LinearAlgebra/QuadraticAnisotropicPerpendicular.lean` and
`Atlas/LinearGroups/Orthogonal/{SiegelSpinor,SiegelReflections}.lean`.
A codimension-two perpendicular space cannot be totally singular in dimension
at least five. Thus a singular parameter splits into two nonsingular ones;
a Siegel transformation with nonsingular parameter is a product of two
reflections. All Dickson, residual and spinor-norm material is omitted.
The proof works in characteristic two. Namespaces, imports and module
boundaries are adapted for CFSG / Lean 4.33.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup

namespace ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

include hQ in
/-- In dimension at least five, a codimension-two perpendicular space cannot be
entirely singular for a polar-nondegenerate quadratic form. -/
theorem exists_anisotropic_perpendicular_pair (hd : 5 ≤ Module.finrank F V)
    (u v : V) : ∃ w : V, Q w ≠ 0 ∧ Q.polarBilin u w = 0 ∧
      Q.polarBilin v w = 0 := by
  classical
  let S : Submodule F V := Submodule.span F {u, v}
  let W := LinearMap.BilinForm.orthogonal Q.polarBilin S
  have hs : Module.finrank F S ≤ 2 := by
    have h := finrank_span_le_card (R := F) ({u, v} : Set V)
    exact h.trans (by simpa using Finset.card_insert_le u ({v} : Finset V))
  have hw : Module.finrank F W = Module.finrank F V - Module.finrank F S :=
    LinearMap.BilinForm.finrank_orthogonal hQ S
  by_contra! hn
  have hz : ∀ w ∈ W, Q w = 0 := by
    intro w hw
    by_contra hnw
    exact hn w hnw (hw u (Submodule.subset_span (by simp)))
      (hw v (Submodule.subset_span (by simp)))
  have hle : W ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W := by
    intro w hw z hz'
    change Q.polarBilin z w = 0
    have h := QuadraticMap.map_add Q z w
    change Q (z+w) = Q z + Q w + Q.polarBilin z w at h
    rw [hz z hz', hz w hw, hz (z+w) (W.add_mem hz' hw), zero_add, zero_add] at h
    exact h.symm
  have hr := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ W] at hr
  omega
end ClassicalOrthogonal.Quadratic

namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (u v : V) (hu : Q u = 0)
  (huv : Q.polarBilin u v = 0) (hv : Q v ≠ 0)

include hu huv in
theorem siegel_reflection_vector_value : Q (v + Q v • u) = Q v := by
  rw [ClassicalOrthogonal.Quadratic.add_smul, hu, polar_swap Q v u, huv]
  ring

/-- A Siegel transformation is a product of two equal-norm reflections. -/
theorem siegelElement_reflection_factor :
    siegelElement Q u v hu huv =
      reflectionElement Q (v + Q v • u) (by rw [siegel_reflection_vector_value Q u v hu huv]; exact hv) *
        reflectionElement Q v hv := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hvu : Q.polarBilin v u = 0 := (polar_swap Q v u).trans huv
  have hp : Q.polarBilin (reflectionLinear Q v hv x) (v + Q v • u) =
      -Q.polarBilin x v + Q v * Q.polarBilin x u := by
    rw [reflectionLinear_apply]
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, polar_self, hvu, mul_zero]
    field_simp
    ring
  change siegel Q u v x = reflectionLinear Q (v + Q v • u) (by rw [siegel_reflection_vector_value Q u v hu huv]; exact hv) (reflectionLinear Q v hv x)
  rw [reflectionLinear_apply, hp, reflectionLinear_apply, siegel_reflection_vector_value Q u v hu huv]
  simp only [siegel, mul_add, mul_neg, smul_add, smul_smul]
  match_scalars <;> field_simp <;> ring

theorem siegelElement_add (w : V) (huw : Q.polarBilin u w = 0) :
    siegelElement Q u v hu huv * siegelElement Q u w hu huw =
      siegelElement Q u (v+w) hu (by rw [map_add, huv, huw, add_zero]) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact siegel_add Q u v w x hu huv huw


end ClassicalOrthogonal.ReflectionGeneration
namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)
  (hd : 5 ≤ Module.finrank F V)

include hQ hd in
theorem isotropic_parameter_anisotropic_sum_stable (u v : V) (hv : Q v = 0)
    (huv : Q.polarBilin u v = 0) :
    ∃ w₁ w₂, v = w₁+w₂ ∧ Q w₁ ≠ 0 ∧ Q w₂ ≠ 0 ∧
      Q.polarBilin u w₁ = 0 ∧ Q.polarBilin u w₂ = 0 := by
  obtain ⟨w, hw, huw, hvw⟩ := exists_anisotropic_perpendicular_pair Q hQ hd u v
  refine ⟨w, v-w, by abel, hw, ?_, huw, ?_⟩
  · have he : Q (v-w) = Q w := by
      rw [sub_value, hv, hvw]
      ring
    rwa [he]
  · rw [map_sub, huv, huw, sub_zero]

omit [FiniteDimensional F V] in
theorem anisotropic_siegel_mem_reflections (u v : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) (hv : Q v ≠ 0) :
    siegelElement Q u v hu huv ∈ reflectionSubgroup Q := by
  rw [siegelElement_reflection_factor Q u v hu huv hv]
  exact (reflectionSubgroup Q).mul_mem (reflectionElement_mem _ _ _)
    (reflectionElement_mem _ _ _)

include hQ hd in
theorem siegel_mem_reflections_stable (u v : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) :
    siegelElement Q u v hu huv ∈ reflectionSubgroup Q := by
  by_cases hv : Q v = 0
  · obtain ⟨w₁, w₂, he, h₁, h₂, hu₁, hu₂⟩ :=
      isotropic_parameter_anisotropic_sum_stable Q hQ hd u v hv huv
    have hs : siegelElement Q u v hu huv =
        siegelElement Q u w₁ hu hu₁ * siegelElement Q u w₂ hu hu₂ := by
      rw [siegelElement_add]
      simp only [he]
    rw [hs]
    exact (reflectionSubgroup Q).mul_mem
      (anisotropic_siegel_mem_reflections Q u w₁ hu hu₁ h₁)
      (anisotropic_siegel_mem_reflections Q u w₂ hu hu₂ h₂)
  · exact anisotropic_siegel_mem_reflections Q u v hu huv hv

include hQ hd in
theorem elementary_le_reflections_stable : elementarySubgroup Q ≤ reflectionSubgroup Q := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  exact siegel_mem_reflections_stable Q hQ hd u v hu huv


end ClassicalOrthogonal.ReflectionGeneration
