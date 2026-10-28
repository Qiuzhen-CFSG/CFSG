module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Comparing fixed subgroups across a centralizing supplement

Suppose D ≤ K and C centralizes K and normalizes U. If D and K have
the same fixed subgroup in U, they also have the same fixed subgroup in
UC. Write an element as cu: since c centralizes D, an element cu fixed
by D has u fixed by D, hence by K.

This is the final fixed-space deduction in Aschbacher–Smith, combined
1 March 2004 manuscript, Lemma 13.6.22, printed p.933.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

/-- Equality of fixed subgroups extends over a supplement centralizing the larger actor. -/
theorem inf_centralizer_eq_of_normalizing_supplement
    (U C K D : Subgroup G) (hDK : D ≤ K)
    (hCK : C ≤ centralizer (K : Set G))
    (hCU : C ≤ normalizer (U : Set G))
    (hfix : U ⊓ centralizer (D : Set G) = U ⊓ centralizer (K : Set G)) :
    (U ⊔ C) ⊓ centralizer (D : Set G) = (U ⊔ C) ⊓ centralizer (K : Set G) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le hDK))
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hprod : x ∈ (C : Set G) * (U : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right C U hCU, sup_comm]
    exact hx.1
  obtain ⟨c, hc, u, hu, he⟩ := hprod
  have hcD : c ∈ centralizer (D : Set G) := centralizer_le hDK (hCK hc)
  have huD : u ∈ centralizer (D : Set G) := by
    have hh := (centralizer (D : Set G)).mul_mem
      ((centralizer (D : Set G)).inv_mem hcD) hx.2
    simpa only [← he, inv_mul_cancel_left] using hh
  have huK := (hfix.le ⟨hu, huD⟩).2
  rw [← he]
  exact (centralizer (K : Set G)).mul_mem (hCK hc) huK
end Subgroup
