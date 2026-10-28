/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Parts adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
The adapted portions are covered by the ATLAS Research and Attribution
License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.Quotient
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.SiegelReflections

/-!
# Elementary transformations in the minus orthogonal commutator

Equal-value reflections are conjugate in the full isometry group. Thus a
Siegel transformation with anisotropic parameter is a commutator. In odd
characteristic and dimension at least three, every perpendicular hyperplane
contains an anisotropic vector; this splits an isotropic parameter into two
anisotropic ones. Consequently every elementary transformation belongs to the
full commutator, including the minus four-space of Witt index one.

For a minus space with at least two hyperbolic pairs, the existing elementary
shell transport makes the full quotient abelian and supplies the reverse
inclusion. The four-dimensional reverse inclusion is deliberately separate.

The reflection-product and Siegel-factor arguments adapt
`Atlas/LinearGroups/Orthogonal/ElementaryDerived.lean`; the perpendicular
argument strengthens the dimension bound of CFSG's `SiegelReflections` in
odd characteristic. We reuse the existing CFSG reflection and quotient APIs,
with Lean 4.33 module boundaries. No perfectness hypothesis is used.
Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup
open scoped commutatorElement
namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- Equal-value reflection products belong to the full commutator, without a Witt-index hypothesis. -/
theorem equal_value_reflection_product_mem_commutator (h2 : (2 : F) ≠ 0)
    (a b : V) (ha : Q a ≠ 0) (hb : Q b ≠ 0) (hab : Q a = Q b) :
    reflectionElement Q b hb * reflectionElement Q a ha ∈
      commutator (quadraticIsometrySubgroup Q) := by
  obtain ⟨g, _, hga⟩ := reflectionSubgroup_transport Q h2 a b ha hab
  have hc : g * reflectionElement Q a ha * g⁻¹ = reflectionElement Q b hb := by
    simpa only [hga] using reflectionElement_conj Q g a ha
  have he : ⁅g, reflectionElement Q a ha⁆ =
      reflectionElement Q b hb * reflectionElement Q a ha := by
    rw [commutatorElement_def, reflectionElement_inv, hc]
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top _)

/-- An anisotropic Siegel parameter gives a product of two conjugate reflections. -/
theorem anisotropic_siegel_mem_commutator_odd (h2 : (2 : F) ≠ 0)
    (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) (hv : Q v ≠ 0) :
    siegelElement Q u v hu huv ∈ commutator (quadraticIsometrySubgroup Q) := by
  rw [siegelElement_reflection_factor Q u v hu huv hv]
  exact equal_value_reflection_product_mem_commutator Q h2 v (v + Q v • u) hv _
    (siegel_reflection_vector_value Q u v hu huv).symm

variable [FiniteDimensional F V]

theorem exists_anisotropic_perpendicular_of_three_le
    (hQ : Q.polarBilin.Nondegenerate) (hd : 3 ≤ Module.finrank F V) (u : V) :
    ∃ w : V, Q w ≠ 0 ∧ Q.polarBilin u w = 0 := by
  classical
  let S : Submodule F V := Submodule.span F {u}
  let W := LinearMap.BilinForm.orthogonal Q.polarBilin S
  have hs : Module.finrank F S ≤ 1 := by
    simpa using finrank_span_le_card (R := F) ({u} : Set V)
  have hw : Module.finrank F W = Module.finrank F V - Module.finrank F S :=
    LinearMap.BilinForm.finrank_orthogonal hQ S
  by_contra! hn
  have hz : ∀ w ∈ W, Q w = 0 := by
    intro w hw
    by_contra hnw
    exact hn w hnw (hw u (Submodule.subset_span (by simp)))
  have hle : W ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W := by
    intro w hw z hz'
    change Q.polarBilin z w = 0
    have h := QuadraticMap.map_add Q z w
    change Q (z + w) = Q z + Q w + Q.polarBilin z w at h
    rw [hz z hz', hz w hw, hz (z + w) (W.add_mem hz' hw), zero_add, zero_add] at h
    exact h.symm
  have hr := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ W] at hr
  omega

theorem isotropic_parameter_anisotropic_sum_odd
    (hQ : Q.polarBilin.Nondegenerate) (hd : 3 ≤ Module.finrank F V)
    (h2 : (2 : F) ≠ 0) (u v : V) (hv : Q v = 0) (huv : Q.polarBilin u v = 0) :
    ∃ w₁ w₂, v = w₁ + w₂ ∧ Q w₁ ≠ 0 ∧ Q w₂ ≠ 0 ∧
      Q.polarBilin u w₁ = 0 ∧ Q.polarBilin u w₂ = 0 := by
  obtain ⟨w, hw, huw⟩ := exists_anisotropic_perpendicular_of_three_le Q hQ hd u
  by_cases hdif : Q (v - w) = 0
  · have hs : Q (v + w) = 2 * Q w := by
      have hm := sub_value Q v w
      have hp := QuadraticMap.map_add Q v w
      change Q (v + w) = Q v + Q w + Q.polarBilin v w at hp
      rw [hv, hdif] at hm
      rw [hv] at hp
      linear_combination hp + hm
    refine ⟨-w, v + w, by abel, ?_, ?_, ?_, ?_⟩
    · rwa [Q.map_neg]
    · rw [hs]
      exact mul_ne_zero h2 hw
    · rw [map_neg, huw, neg_zero]
    · rw [map_add, huv, huw, add_zero]
  · refine ⟨w, v - w, by abel, hw, hdif, huw, ?_⟩
    rw [map_sub, huv, huw, sub_zero]

theorem siegel_mem_commutator_odd
    (hQ : Q.polarBilin.Nondegenerate) (hd : 3 ≤ Module.finrank F V)
    (h2 : (2 : F) ≠ 0) (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    siegelElement Q u v hu huv ∈ commutator (quadraticIsometrySubgroup Q) := by
  by_cases hv : Q v = 0
  · obtain ⟨w₁, w₂, he, h₁, h₂, hu₁, hu₂⟩ :=
      isotropic_parameter_anisotropic_sum_odd Q hQ hd h2 u v hv huv
    have he' : siegelElement Q u v hu huv =
        siegelElement Q u w₁ hu hu₁ * siegelElement Q u w₂ hu hu₂ := by
      rw [siegelElement_add]
      simp only [he]
    rw [he']
    exact Subgroup.mul_mem _
      (anisotropic_siegel_mem_commutator_odd Q h2 u w₁ hu hu₁ h₁)
      (anisotropic_siegel_mem_commutator_odd Q h2 u w₂ hu hu₂ h₂)
  · exact anisotropic_siegel_mem_commutator_odd Q h2 u v hu huv hv

theorem elementary_le_commutator_odd
    (hQ : Q.polarBilin.Nondegenerate) (hd : 3 ≤ Module.finrank F V)
    (h2 : (2 : F) ≠ 0) : elementarySubgroup Q ≤ commutator (quadraticIsometrySubgroup Q) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  exact siegel_mem_commutator_odd Q hQ hd h2 u v hu huv

end ClassicalOrthogonal.ReflectionGeneration

namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
variable {F : Type*} [Field F] [Finite F]

/-- Elementary containment on the literal minus complement, including dimension four and F₃. -/
theorem complement_elementary_le_omega (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (Minus.quadraticForm F (r + 1)) ≤
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) := by
  apply elementary_le_commutator_odd _ (Minus.quadraticForm_nonsingular F (r + 1)) _ h2
  rw [Minus.space_finrank]
  omega

/-- The first two hyperbolic pairs in the actual minus coordinate space. -/
def minusWittTwoFrame (r : ℕ) (hr : 2 ≤ r) :
    WittTwoFrame (Minus.quadraticForm F (r + 1)) where
  e₁ := (fun j => (if j = (⟨0, by omega⟩ : Fin r) then 1 else 0, 0), 0)
  f₁ := (fun j => (0, if j = (⟨0, by omega⟩ : Fin r) then 1 else 0), 0)
  e₂ := (fun j => (if j = (⟨1, by omega⟩ : Fin r) then 1 else 0, 0), 0)
  f₂ := (fun j => (0, if j = (⟨1, by omega⟩ : Fin r) then 1 else 0), 0)
  qe₁ := by simp [Minus.quadraticForm]
  qf₁ := by simp [Minus.quadraticForm]
  qe₂ := by simp [Minus.quadraticForm]
  qf₂ := by simp [Minus.quadraticForm]
  pair₁ := by
    change (Minus.form F r _).polarBilin _ _ = 1
    rw [Minus.form_polar]
    simp
  pair₂ := by
    change (Minus.form F r _).polarBilin _ _ = 1
    rw [Minus.form_polar]
    simp
  ee := by
    change (Minus.form F r _).polarBilin _ _ = 0
    rw [Minus.form_polar]
    simp
  ef := by
    change (Minus.form F r _).polarBilin _ _ = 0
    rw [Minus.form_polar]
    simp
  fe := by
    change (Minus.form F r _).polarBilin _ _ = 0
    rw [Minus.form_polar]
    simp
  ff := by
    change (Minus.form F r _).polarBilin _ _ = 0
    rw [Minus.form_polar]
    simp

/-- The complementary elementary and full commutator subgroups coincide for at least two hyperbolic pairs. -/
theorem complement_elementary_eq_omega_of_two_le (r : ℕ) (hr : 2 ≤ r)
    (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (Minus.quadraticForm F (r + 1)) =
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) := by
  apply le_antisymm (complement_elementary_le_omega r (by omega) h2)
  let := SplitOddBlocks.elementary_normal (Minus.quadraticForm F (r + 1))
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    (SplitOddBlocks.IsometryQuotients.elementaryQuotient_isMulCommutative _
      (minusWittTwoFrame r hr) (Minus.quadraticForm_nonsingular F (r + 1)) h2)

end ClassicalOrthogonal.Fundamental.MinusCentralizer
