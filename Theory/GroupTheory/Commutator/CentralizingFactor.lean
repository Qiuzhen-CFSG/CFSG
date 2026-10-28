module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Removing a centralizing factor from a commutator

If `X = A Q` and `Q` centralizes `V`, then `[V,X] = [V,A]`: factor each
commutator's second entry and cancel the commutator with `Q`. No ambient
normality or finiteness is required.

This is the final calculation in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), Lemma 4.1.5(3), p. 608.
-/

public section

namespace Subgroup

open scoped Pointwise commutatorElement
variable {G : Type*} [Group G]

theorem commutator_eq_of_product_centralizing_factor {V X A Q : Subgroup G}
    (hX : (X : Set G) = (A : Set G) * (Q : Set G))
    (hQ : V ≤ centralizer (Q : Set G)) : ⁅V, X⁆ = ⁅V, A⁆ := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro v hv x hx
    have hx' : x ∈ (X : Set G) := hx
    obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.mp (hX ▸ hx')
    have hcomm : ⁅v, q⁆ = 1 := by
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_iff.mp (hQ hv) q hq).symm
    simpa only [commutatorElement_mul_right_eq_mul_conj, hcomm, mul_one,
      mul_inv_cancel_right] using (commutator_mem_commutator hv ha : ⁅v, a⁆ ∈ ⁅V, A⁆)
  · apply commutator_mono le_rfl
    intro a ha
    change a ∈ (X : Set G)
    rw [hX]
    exact Set.mem_mul.mpr ⟨a, ha, 1, Q.one_mem, mul_one a⟩

end Subgroup
