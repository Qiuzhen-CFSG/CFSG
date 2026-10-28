module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Normalizing a join from a commutator bound

If V is normal, Z is contained in H, and [H,E] is contained in V, then E
normalizes Z joined with V. No finiteness or normality of H or E is needed.
This is the elementary normalization step applied to ZV in the
noncentralizing case of Stellmacher (2.3), Journal of Algebra 190 (1997).

Write an element of the join as zv. Conjugating z by an element of E
changes z by a commutator in V; conjugating v stays in V by normality.
Both factors therefore remain in the join, giving the normalizer bound.
-/

open scoped commutatorElement

namespace Subgroup

public theorem le_normalizer_sup_of_commutator_le
    {G : Type*} [Group G] (H E Z V : Subgroup G) [V.Normal]
    (hZH : Z ≤ H) (hcomm : ⁅H, E⁆ ≤ V) :
    E ≤ Subgroup.normalizer ((Z ⊔ V : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro e he x hx
  obtain ⟨z, hz, v, hv, rfl⟩ := mem_sup_of_normal_right.mp hx
  have hcz : ⁅e, z⁆ ∈ V := by
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator he (hZH hz))
  have hez : e * z * e⁻¹ ∈ Z ⊔ V := by
    have hh := (Z ⊔ V).mul_mem ((show V ≤ Z ⊔ V from le_sup_right) hcz)
      ((show Z ≤ Z ⊔ V from le_sup_left) hz)
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
  have hev : e * v * e⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem v hv e
  have hh := (Z ⊔ V).mul_mem hez ((show V ≤ Z ⊔ V from le_sup_right) hev)
  simpa only [mul_assoc, inv_mul_cancel_left] using hh

end Subgroup

