module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
Under an inner-action cover K C_G(K), the centralizer of R≤K lies in C_K(R) C_G(K).
Source application: Aschbacher--Smith 2.5.15, printed pp.558--559.
-/

public section
namespace Subgroup
open scoped Pointwise
variable {G : Type*} [Group G]

theorem centralizer_inf_le_sup_of_inner_cover
    (K Y R : Subgroup G) (hR : R ≤ K) (hY : Y ≤ K ⊔ centralizer (K : Set G)) :
    Y ⊓ centralizer (R : Set G) ≤ (K ⊓ centralizer (R : Set G)) ⊔ centralizer (K : Set G) := by
  intro x hx
  have hm : x ∈ (K : Set G) * (centralizer (K : Set G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K _ (centralizer_le_normalizer _)]
    exact hY hx.1
  obtain ⟨k,hk,c,hc,rfl⟩ := hm
  have hcR : c ∈ centralizer (R : Set G) := centralizer_le hR hc
  have hkR : k ∈ centralizer (R : Set G) := by
    have hh := (centralizer (R : Set G)).mul_mem hx.2 ((centralizer (R : Set G)).inv_mem hcR)
    simpa only [mul_inv_cancel_right] using hh
  exact mul_mem (mem_sup_left ⟨hk,hkR⟩) (mem_sup_right hc)

end Subgroup
