module

public import Theory.Character.ClassFunctionSum
public import Theory.Character.InvolutionSectionVanishing
public import Theory.Character.ModularBlock.Congruence
public import Theory.Character.ModularBlock.SectionRelation
public import Mathlib.GroupTheory.PGroup

/-!
# Vanishing and averaging involution-weighted principal-block columns

If no conjugate of an involution `J` inverts a two-element `u`, the ordinary
involution-weighted character relation vanishes throughout the two-section
of `u`. The actual principal-block projection preserves this relation by
`SectionRelation`, proving the block-restricted pointwise identity.

Finite-sum interchange identifies the weighted sum of restriction scalar
products with the scalar product against the pointwise weighted column.
Consequently pointwise vanishing on the support of a function implies the
averaged identity. The argument works for arbitrary complex-valued functions,
in particular for generalized characters on two-subgroups.

Source: Brauer, *Some applications of the theory of blocks of characters
of finite groups II* (1964), Section IV, Proposition 4 and Corollary 1,
pp. 312–313, and Section V, Lemma 4, equation (5.4), p. 316.
-/

public section
noncomputable section

namespace ModularBlock.InvolutionColumnVanishing

open scoped BigOperators
open PrincipalBlockConstruction
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

/-- Brauer's principal-block involution identity: the weighted column at a
two-element vanishes if no conjugate of the involution inverts it. -/
theorem principalBlock_involution_weighted_column_eq_zero
    (d : PrincipalCongruenceBlockData G) (u J : G)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (hJ : orderOf J = 2)
    (hno : ∀ t : G, IsConj J t → t * u * t⁻¹ ≠ u⁻¹) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk u) * d.chi i (ConjClasses.mk J) ^ 2 /
      d.chi i (ConjClasses.mk 1) = 0 := by
  have hJ2 : J * J = 1 := by simpa only [hJ, pow_two] using pow_orderOf_eq_one J
  have h := SectionRelation.sum_block_eq_zero_of_vanishes_on_twoSection d u hu
    (fun i => d.chi i (ConjClasses.mk J) ^ 2 / d.chi i (ConjClasses.mk 1)) (by
      intro v hv hc
      simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        Theory.Character.involution_weighted_sum_eq_zero_on_twoSection
          d.chi d.complete u J hu hJ2 hno v hv hc)
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- The finite-sum interchange in Brauer's averaged involution identity. -/
theorem principalBlock_involution_weighted_scalarProduct
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (θ : ClassFunction Q) (J : G) :
    ∑ i ∈ d.block,
        scalarProduct Q (fun q => d.chi i (ConjClasses.mk (q : G))) θ *
          d.chi i (ConjClasses.mk J) ^ 2 / d.chi i (ConjClasses.mk 1) =
      scalarProduct Q
        (fun q => ∑ i ∈ d.block, d.chi i (ConjClasses.mk (q : G)) *
          d.chi i (ConjClasses.mk J) ^ 2 / d.chi i (ConjClasses.mk 1)) θ := by
  simpa only [mul_div_assoc] using sum_scalarProduct_mul d.block
    (fun i (q : Q) => d.chi i (ConjClasses.mk (q : G))) θ
    (fun i => d.chi i (ConjClasses.mk J) ^ 2 / d.chi i (ConjClasses.mk 1))

/-- Averaging a pointwise zero column gives a zero restriction column sum.
Only values in the support of `θ` are needed. -/
theorem principalBlock_involution_weighted_sum_eq_zero_of_pointwise
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (θ : ClassFunction Q) (J : G)
    (hvanish : ∀ q : Q, θ q ≠ 0 →
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk (q : G)) *
        d.chi i (ConjClasses.mk J) ^ 2 / d.chi i (ConjClasses.mk 1) = 0) :
    ∑ i ∈ d.block,
        scalarProduct Q (fun q => d.chi i (ConjClasses.mk (q : G))) θ *
          d.chi i (ConjClasses.mk J) ^ 2 / d.chi i (ConjClasses.mk 1) = 0 := by
  classical
  rw [principalBlock_involution_weighted_scalarProduct, scalarProduct]
  apply mul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : θ q = 0
  · simp only [hq, star_zero, mul_zero]
  · rw [hvanish q hq, zero_mul]

/-- Brauer's averaged identity on a two-subgroup. It holds for every complex
function supported on elements inverted by no conjugate of `J`, and hence
in particular for every generalized character with that support. -/
theorem principalBlock_involution_weighted_sum_eq_zero
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) (θ : ClassFunction Q) (J : G) (hJ : orderOf J = 2)
    (hsupport : ∀ q : Q, θ q ≠ 0 →
      ∀ t : G, IsConj J t → t * (q : G) * t⁻¹ ≠ (q : G)⁻¹) :
    ∑ i ∈ d.block,
        scalarProduct Q (fun q => d.chi i (ConjClasses.mk (q : G))) θ *
          d.chi i (ConjClasses.mk J) ^ 2 / d.chi i (ConjClasses.mk 1) = 0 := by
  apply principalBlock_involution_weighted_sum_eq_zero_of_pointwise
  intro q hq
  apply principalBlock_involution_weighted_column_eq_zero d q J _ hJ (hsupport q hq)
  obtain ⟨n, hn⟩ := hQ.exists_pow_pow_eq_one q
  exact ⟨n, congrArg Q.subtype hn⟩

end ModularBlock.InvolutionColumnVanishing
