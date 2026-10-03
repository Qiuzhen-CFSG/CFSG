module

public import Theory.Character.ModularBlock.SectionOrthogonality
public import Theory.Character.Orthogonality

/-!
# Recovering principal-block relations from the character kernel

The projection of any complex linear combination of ordinary irreducible
characters onto the principal block is recovered by averaging against the
block's column kernel. This follows from ordinary row orthogonality and
interchanging the finite sums.

The imported `SectionOrthogonality` proves that this kernel is supported on
the two-section of its base two-element, using the odd-order twisted integral
permutation trace argument. Consequently, a relation vanishing on the section
still vanishes at its two-element after principal-block projection. The final
theorem applies this support result to the actual principal block, without
additional orthogonality or decomposition-matrix hypotheses.

Source: Brauer, *Some applications of the theory of blocks of characters
of finite groups II* (1964), §IV, Proposition 4, p.313. The kernel argument
is an alternative to the generalized-decomposition proof given there.
-/

public section
noncomputable section

open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction
attribute [local instance] Fintype.ofFinite

namespace ModularBlock.SectionRelation
variable {G : Type*} [Group G] [Finite G]

/-- Row orthogonality reconstructs the block projection using its column kernel. -/
theorem sum_block_eq_kernel (d : PrincipalCongruenceBlockData G)
    (a : d.I → ℂ) (u : G) :
    ∑ i ∈ d.block, a i * d.chi i (ConjClasses.mk u) =
      (Nat.card G : ℂ)⁻¹ * ∑ g : G,
        (∑ i, a i * d.chi i (ConjClasses.mk g)) *
          ∑ i ∈ d.block, d.chi i (ConjClasses.mk u) *
            star (d.chi i (ConjClasses.mk g)) := by
  classical
  have hcoeff (j : d.I) :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G,
        (∑ i, a i * d.chi i (ConjClasses.mk g)) *
          star (d.chi j (ConjClasses.mk g)) = a j := by
    have h := classFunctionInner_sum_left a d.chi (d.chi j)
    simp only [smul_eq_mul, completeFamily_orthonormal d.complete] at h
    simpa [classFunctionInner, Finset.sum_apply, Pi.smul_apply] using h
  symm
  calc
    _ = (Nat.card G : ℂ)⁻¹ * ∑ i ∈ d.block, ∑ g : G,
        ((∑ j, a j * d.chi j (ConjClasses.mk g)) *
          star (d.chi i (ConjClasses.mk g))) * d.chi i (ConjClasses.mk u) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro g hg
      ring
    _ = ∑ i ∈ d.block,
        ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
          (∑ j, a j * d.chi j (ConjClasses.mk g)) *
            star (d.chi i (ConjClasses.mk g))) * d.chi i (ConjClasses.mk u) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = _ := by simp_rw [hcoeff]

/-- Kernel support on a two-section suffices to preserve a relation at its two-element.
The support premise is a separate modular theorem, not part of the relation datum. -/
theorem sum_block_eq_zero_of_kernel_support (d : PrincipalCongruenceBlockData G)
    (u : G)
    (hsupport : ∀ g : G,
      (¬ ∃ v : G, Odd (orderOf v) ∧ Commute u v ∧ IsConj (u * v) g) →
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk u) *
        star (d.chi i (ConjClasses.mk g)) = 0)
    (a : d.I → ℂ)
    (hrelation : ∀ v : G, Odd (orderOf v) → Commute u v →
      ∑ i, a i * d.chi i (ConjClasses.mk (u * v)) = 0) :
    ∑ i ∈ d.block, a i * d.chi i (ConjClasses.mk u) = 0 := by
  classical
  rw [sum_block_eq_kernel]
  suffices h : (∑ g : G, (∑ i, a i * d.chi i (ConjClasses.mk g)) *
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk u) *
        star (d.chi i (ConjClasses.mk g))) = 0 by rw [h, mul_zero]
  apply Finset.sum_eq_zero
  intro g hg
  by_cases h : ∃ v : G, Odd (orderOf v) ∧ Commute u v ∧ IsConj (u * v) g
  · obtain ⟨v, hv, hc, hconj⟩ := h
    rw [← ConjClasses.mk_eq_mk_iff_isConj.mpr hconj, hrelation v hv hc, zero_mul]
  · rw [hsupport g h, mul_zero]

/-- A relation on a two-section remains zero at its two-element after projection
onto the actual principal two-block. -/
theorem sum_block_eq_zero_of_vanishes_on_twoSection
    (d : PrincipalCongruenceBlockData G) (u : G)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (a : d.I → ℂ)
    (hrelation : ∀ v : G, Odd (orderOf v) → Commute u v →
      ∑ i, a i * d.chi i (ConjClasses.mk (u * v)) = 0) :
    ∑ i ∈ d.block, a i * d.chi i (ConjClasses.mk u) = 0 := by
  exact sum_block_eq_zero_of_kernel_support d u
    (SectionOrthogonality.principalBlock_column_eq_zero_of_not_mem_twoSection d u hu)
    a hrelation

end ModularBlock.SectionRelation
