module

public import Theory.Representation.TensorInvolutionDisplacement
public import Mathlib.RepresentationTheory.Invariants

/-!
# Cyclic fixed codimensions of tensor involutions

The cyclic invariant subspace is exactly the kernel of the generator minus
one. The checked exchanged-pair decomposition of a characteristic-two
involution therefore gives the tensor rank identity for the actual
`Representation.tprod` and its literal cyclic fixed-space quotient. The
half-dimension upper bound on each displacement gives both multiplicative
lower bounds used by the exceptional Ree tensor estimate.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 2.9
and Corollary 2.11(a), internal pp.9--10.
-/

public section

open Module
open scoped TensorProduct
open Representation.BinaryOffender.NaturalTensor

namespace Representation.TensorInvolutionDisplacement

variable {K G U W : Type*} [Field K] [Group G]
  [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]

/-- Fixing a cyclic group is equivalent to fixing its specified generator. -/
theorem invariants_zpowers_eq_ker (ρ : Representation K G U) (t : G) :
    invariants (ρ.comp (Subgroup.zpowers t).subtype) = LinearMap.ker (ρ t - 1) := by
  let z : Subgroup.zpowers t := ⟨t, Subgroup.mem_zpowers t⟩
  have hz : ∀ x : Subgroup.zpowers t, x ∈ Subgroup.zpowers z := by
    intro x
    obtain ⟨i, hi⟩ := x.property
    exact ⟨i, Subtype.ext hi⟩
  ext v
  rw [mem_invariants_iff_of_forall_mem_zpowers _ z hz]
  change ρ t v = v ↔ ρ t v - v = 0
  exact sub_eq_zero.symm

/-- The displacement rank is the dimension of the literal cyclic quotient. -/
theorem operatorFixedCodim_eq_cyclicFixedCodim (ρ : Representation K G U) (t : G) :
    operatorFixedCodim (ρ t) =
      finrank K (U ⧸ invariants (ρ.comp (Subgroup.zpowers t).subtype)) := by
  rw [invariants_zpowers_eq_ker, operatorFixedCodim_eq_finrank_quotient]

variable [CharP K 2] [FiniteDimensional K U] [FiniteDimensional K W]

/-- The tensor rank identity for actual representations, without subtraction. -/
theorem tprod_displacement_formula (ρ : Representation K G U) (σ : Representation K G W)
    (t : G) (ht : t ^ 2 = 1) :
    operatorFixedCodim ((ρ.tprod σ) t) +
      2 * operatorFixedCodim (ρ t) * operatorFixedCodim (σ t) =
      finrank K W * operatorFixedCodim (ρ t) +
        finrank K U * operatorFixedCodim (σ t) := by
  exact tensor_displacement_formula (ρ t) (σ t)
    (by rw [← map_mul, ← pow_two, ht, map_one])
    (by rw [← map_mul, ← pow_two, ht, map_one])

/-- Tensoring multiplies the first displacement lower bound by the second dimension. -/
theorem mul_finrank_le_tprod_displacement_left
    (ρ : Representation K G U) (σ : Representation K G W) (t : G) (ht : t ^ 2 = 1) :
    operatorFixedCodim (ρ t) * finrank K W ≤ operatorFixedCodim ((ρ.tprod σ) t) := by
  have hf := tprod_displacement_formula ρ σ t ht
  have ha := twice_displacement_le (ρ t)
    (by rw [← map_mul, ← pow_two, ht, map_one])
  nlinarith [Nat.mul_le_mul_right (operatorFixedCodim (σ t)) ha]

/-- The symmetric displacement lower bound from the second tensor factor. -/
theorem mul_finrank_le_tprod_displacement_right
    (ρ : Representation K G U) (σ : Representation K G W) (t : G) (ht : t ^ 2 = 1) :
    finrank K U * operatorFixedCodim (σ t) ≤ operatorFixedCodim ((ρ.tprod σ) t) := by
  have hf := tprod_displacement_formula ρ σ t ht
  have hb := twice_displacement_le (σ t)
    (by rw [← map_mul, ← pow_two, ht, map_one])
  nlinarith [Nat.mul_le_mul_right (operatorFixedCodim (ρ t)) hb]

/-- The tensor identity expressed using the literal cyclic fixed-space quotients. -/
theorem tprod_cyclicFixedCodim_formula
    (ρ : Representation K G U) (σ : Representation K G W) (t : G) (ht : t ^ 2 = 1) :
    finrank K ((U ⊗[K] W) ⧸ invariants ((ρ.tprod σ).comp (Subgroup.zpowers t).subtype)) +
      2 * finrank K (U ⧸ invariants (ρ.comp (Subgroup.zpowers t).subtype)) *
        finrank K (W ⧸ invariants (σ.comp (Subgroup.zpowers t).subtype)) =
      finrank K W * finrank K (U ⧸ invariants (ρ.comp (Subgroup.zpowers t).subtype)) +
        finrank K U * finrank K (W ⧸ invariants (σ.comp (Subgroup.zpowers t).subtype)) := by
  simpa only [operatorFixedCodim_eq_cyclicFixedCodim] using tprod_displacement_formula ρ σ t ht

end Representation.TensorInvolutionDisplacement
