module
public import Theory.Character.BrauerTuanAveraging

/-!
# Character kernels and the Brauer--Tuan intersection argument

A restricted column kernel recovers its selected character coefficients by
ordinary row orthogonality. Thus two column kernels with disjoint supports
have zero pairing, which gives vanishing of the column sum over their common
rows. Averaging that sum on a subgroup gives algebraic-integral divisibility.

For Brauer--Tuan Lemma 3, the first support consists of the `p`-singular
elements. In the absence of elements of order `pq`, those elements are
`q`-regular, and `q`-block orthogonality supplies the second vanishing kernel.
These results isolate the ordinary-character argument from the construction
of block projectors at arbitrary primes.

Source: Brauer--Tuan, *On simple groups of finite order I*, Bull. AMS 51
(1945), proof of Lemma 3, pp.764--765, equations (4.8)--(4.13).
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace BrauerTuan
variable {G I : Type*} [Group G] [Finite G] [Fintype I] [DecidableEq I]

/-- Averaging a restricted character column recovers precisely its selected rows. -/
theorem restricted_column_average (χ : I → ConjClassFunction G)
    (hχ : IsCompleteIrreducibleCharacterFamily χ) (A : Finset I) (u : G) (j : I) :
    (Nat.card G : ℂ)⁻¹ * ∑ g : G,
      (∑ i ∈ A, χ i (ConjClasses.mk u) * star (χ i (ConjClasses.mk g))) *
        χ j (ConjClasses.mk g) =
      if j ∈ A then χ j (ConjClasses.mk u) else 0 := by
  classical
  calc
    _ = ∑ i ∈ A, χ i (ConjClasses.mk u) * classFunctionInner (χ j) (χ i) := by
      simp only [Finset.sum_mul, classFunctionInner]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [mul_left_comm]
      congr 2
      apply Finset.sum_congr rfl
      intro g hg
      exact mul_comm _ _
    _ = ∑ i ∈ A, χ i (ConjClasses.mk u) * (if j = i then 1 else 0) := by
      simp only [completeFamily_orthonormal hχ]
    _ = _ := by simp [mul_ite]

/-- Two restricted column kernels with disjoint supports give a vanishing
column sum over the intersection of their row sets. -/
theorem intersection_column_eq_zero_of_kernel_support
    (χ : I → ConjClassFunction G) (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (A B : Finset I) (u v : G) (S : G → Prop)
    (hA : ∀ g, ¬ S g →
      ∑ i ∈ A, χ i (ConjClasses.mk u) * star (χ i (ConjClasses.mk g)) = 0)
    (hB : ∀ g, S g →
      ∑ i ∈ B, χ i (ConjClasses.mk g) * χ i (ConjClasses.mk v) = 0) :
    ∑ i ∈ A ∩ B, χ i (ConjClasses.mk u) * χ i (ConjClasses.mk v) = 0 := by
  classical
  let f (g : G) := ∑ i ∈ A, χ i (ConjClasses.mk u) * star (χ i (ConjClasses.mk g))
  have hzero (g : G) : f g *
      (∑ i ∈ B, χ i (ConjClasses.mk g) * χ i (ConjClasses.mk v)) = 0 := by
    by_cases hg : S g
    · rw [hB g hg, mul_zero]
    · rw [show f g = 0 from hA g hg, zero_mul]
  have heq : (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g *
      (∑ i ∈ B, χ i (ConjClasses.mk g) * χ i (ConjClasses.mk v)) =
      ∑ i ∈ A ∩ B, χ i (ConjClasses.mk u) * χ i (ConjClasses.mk v) := by
    calc
      _ = ∑ i ∈ B,
          ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * χ i (ConjClasses.mk g)) *
            χ i (ConjClasses.mk v) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [← mul_assoc, ← Finset.sum_mul]
      _ = ∑ i ∈ B,
          (if i ∈ A then χ i (ConjClasses.mk u) else 0) * χ i (ConjClasses.mk v) := by
        simp only [f, restricted_column_average χ hχ]
      _ = _ := by
        rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
        simp only [ite_mul, zero_mul]
  rw [← heq]
  simp only [hzero, Finset.sum_const_zero, mul_zero]

/-- The subgroup-divisibility conclusion of the intersection argument, assuming
only the two required kernel support statements. -/
theorem isIntegral_intersection_sum_div_card_of_kernel_support
    (χ : I → ConjClassFunction G) (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (A B : Finset I) (u : G) (H : Subgroup G) (S : G → Prop)
    (hA : ∀ g, ¬ S g →
      ∑ i ∈ A, χ i (ConjClasses.mk u) * star (χ i (ConjClasses.mk g)) = 0)
    (hB : ∀ x : H, x ≠ 1 → ∀ g, S g →
      ∑ i ∈ B, χ i (ConjClasses.mk g) * χ i (ConjClasses.mk (x : G)) = 0) :
    IsIntegral ℤ ((∑ i ∈ A ∩ B, χ i (ConjClasses.mk 1) *
      χ i (ConjClasses.mk u)) / (Nat.card H : ℂ)) := by
  classical
  have hi : ∀ i ∈ A ∩ B, IsIntegral ℤ (χ i (ConjClasses.mk u)) := by
    intro i _
    obtain ⟨n, ρ, hρ⟩ := (hχ.1 i).1
    rw [hρ]
    exact character_value_isIntegral ρ u
  have hv : ∀ x : H, x ≠ 1 → ∑ i ∈ A ∩ B,
      χ i (ConjClasses.mk u) * χ i (ConjClasses.mk (x : G)) = 0 := by
    intro x hx
    exact intersection_column_eq_zero_of_kernel_support χ hχ A B u x S hA (hB x hx)
  simpa only [mul_comm] using isIntegral_degree_sum_div_card_of_vanishing
    (A ∩ B) χ (fun i _ => (hχ.1 i).1) (fun i => χ i (ConjClasses.mk u)) hi H hv

end BrauerTuan
