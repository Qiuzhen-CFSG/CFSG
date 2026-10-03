module
public import Theory.Character.ModularBlock.RestrictionColumn

/-!
# Bounds for entries of restriction columns

Pairing a restriction with the degree-zero difference ψ - zθ gives the integer
cψ - z cθ. Each square is bounded by the sum of squares of the full principal
block column. This elementary bridge allows a column isometry to supply the
integral inequalities needed in restriction-degree estimates.

Source application: Glauberman, *A Characterization of the Suzuki Groups*
(1968), the inequality preceding equation (4.6), p. 89.
-/

open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.RestrictionColumn
variable {G : Type*} [Group G] [Finite G]

/-- An integer column's self-pairing computes the squared norm of the actual
restriction scalar products. This converts a complex-valued column isometry
into the real norm identity used by entry bounds. -/
public theorem norm_sum_eq_of_coefficient_self_pairing
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (θ : ClassFunction H) (hθ : IsGeneralizedCharacter θ) (r : ℝ)
    (hpair : ∑ i ∈ d.block,
      (coefficient d H θ hθ i : ℂ) * (coefficient d H θ hθ i : ℂ) = (r : ℂ)) :
    ∑ i ∈ d.block, Complex.normSq (scalarProduct H (restriction d H i) θ) = r := by
  apply Complex.ofReal_injective
  push_cast
  rw [← hpair]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← coefficient_cast d H θ hθ hi, Complex.normSq_intCast]
  push_cast
  rfl

/-- A norm bound on the actual restriction column bounds each integral entry. -/
public theorem multiplicity_difference_sq_le_of_norm_sum_le
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (ψ θ : ClassFunction H) (z : ℕ) {i : d.I} (hi : i ∈ d.block)
    (cψ cθ : ℕ)
    (hcψ : scalarProduct H (restriction d H i) ψ = cψ)
    (hcθ : scalarProduct H (restriction d H i) θ = cθ)
    (hsum : ∑ k ∈ d.block,
      Complex.normSq (scalarProduct H (restriction d H k) (ψ - (z : ℂ) • θ)) ≤
        1 + (z : ℝ) ^ 2) :
    ((cψ : ℤ) - (z : ℤ) * cθ) ^ 2 ≤ 1 + (z : ℤ) ^ 2 := by
  have he : scalarProduct H (restriction d H i) (ψ - (z : ℂ) • θ) =
      (((cψ : ℤ) - (z : ℤ) * cθ : ℤ) : ℂ) := by
    have hsub : scalarProduct H (restriction d H i) (ψ - (z : ℂ) • θ) =
        scalarProduct H (restriction d H i) ψ -
          scalarProduct H (restriction d H i) ((z : ℂ) • θ) := by
      simp only [scalarProduct, Pi.sub_apply, star_sub, mul_sub, Finset.sum_sub_distrib]
    rw [hsub, scalarProduct_smul_right, hcψ, hcθ]
    simp only [star_natCast, Int.cast_sub, Int.cast_natCast, Int.cast_mul]
    ring
  have hb := (Finset.single_le_sum (fun k (_ : k ∈ d.block) =>
    Complex.normSq_nonneg (scalarProduct H (restriction d H k) (ψ - (z : ℂ) • θ))) hi).trans hsum
  rw [he, Complex.normSq_intCast, ← sq] at hb
  exact_mod_cast hb

end ModularBlock.RestrictionColumn
