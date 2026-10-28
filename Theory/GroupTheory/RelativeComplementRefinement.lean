module
public import Theory.GroupTheory.RelativeComplementProjection
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Refining a relative subgroup complement

Suppose V, W and K generate H, V is normal in H, and K normalizes W.
If V and W are disjoint and K is disjoint from their join, then WK is
an actual complement to V inside H. The proof uses the unique product
factorization of WK to establish its disjointness from V.

This is the subgroup step used to construct the parabolic complement in
Aschbacher--Smith, 12.2.26, printed p.806. Normality is only inside H.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

theorem disjoint_sup_of_normalizes_right_factor (V W K : Subgroup G)
    (hWK : K ≤ normalizer (W : Set G))
    (hVW : Disjoint V W) (hVK : Disjoint (V ⊔ W) K) :
    Disjoint V (W ⊔ K) := by
  apply disjoint_def.mpr
  intro x hxV hxWK
  have hxprod : x ∈ (W : Set G) * (K : Set G) := by
    rwa [← coe_mul_of_right_le_normalizer_left W K hWK]
  obtain ⟨w, hw, k, hk, rfl⟩ := hxprod
  have hkVW : k ∈ V ⊔ W := by
    have hh := (V ⊔ W).mul_mem
      ((V ⊔ W).inv_mem (mem_sup_right hw)) (mem_sup_left hxV)
    simpa only [inv_mul_cancel_left] using hh
  have hk1 := disjoint_def.mp hVK hkVW hk
  simp only [hk1, mul_one] at hxV ⊢
  exact disjoint_def.mp hVW hxV hw

/-- Refine a three-factor decomposition into a complement to the first factor.
Only relative normality in the displayed overgroup is required. -/
theorem relative_complement_refinement (H V W K : Subgroup G)
    (hVH : V ≤ H) (hWH : W ≤ H) (hKH : K ≤ H)
    (hgen : V ⊔ W ⊔ K = H) (hWK : K ≤ normalizer (W : Set G))
    (hVW : Disjoint V W) (hVK : Disjoint (V ⊔ W) K)
    [(V.subgroupOf H).Normal] :
    (V.subgroupOf H).IsComplement' ((W ⊔ K).subgroupOf H) := by
  apply IsComplement'.symm
  exact relative_isComplement hVH (sup_le hWH hKH) (sup_assoc V W K ▸ hgen)
    (disjoint_sup_of_normalizes_right_factor V W K hWK hVW hVK)

end Subgroup
