module
public import Theory.GroupTheory.PCoreImage
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The two-core of a point intersection in a smaller overgroup

Suppose P≤M, P normalizes K, and K∩M≤P. For R=O₂(P), the intersection
KR∩M lies normally in P and contains R. Its two-core is therefore exactly R.
Normality is relative to P; K need not be normal in the ambient group.

The selected-component applications in Chapter13 retain the original point
radical while replacing KT by KR=K R(T∩K).
Source: Aschbacher–Smith 13.4.10, printed p.908.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

/-- If P normalizes K and contains K∩M, restriction to KR∩M retains O₂(P). -/
theorem point_twoCore_eq_of_normalized_join
    (K P M : Subgroup G) (hPM : P ≤ M)
    (hPK : P ≤ normalizer (K : Set G)) (hKM : K ⊓ M ≤ P) :
    ((K ⊔ P.pCoreIn 2) ⊓ M).pCoreIn 2 = P.pCoreIn 2 := by
  let R := P.pCoreIn 2
  let X := K ⊔ R
  let C := X ⊓ M
  have hRP : R ≤ P := pCoreIn_le 2 P
  have hPR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hCP : C ≤ P := by
    rintro x ⟨hx,hxM⟩
    have hx' : x ∈ (K : Set G) * (R : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left K R (hRP.trans hPK)]
      exact hx
    obtain ⟨k,hk,r,hr,rfl⟩ := hx'
    have hkM := M.mul_mem hxM (M.inv_mem (hPM (hRP hr)))
    rw [mul_inv_cancel_right] at hkM
    exact P.mul_mem (hKM ⟨hk,hkM⟩) (hRP hr)
  have hPC : P ≤ normalizer (C : Set G) :=
    (le_inf ((le_inf hPK hPR).trans (normalizer_inf_normalizer_le_normalizer_sup K R))
      (hPM.trans M.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  exact le_antisymm (pCoreIn_mono_of_normalizes hCP hPC)
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 P)
      (le_inf le_sup_right (hRP.trans hPM)) (hCP.trans hPR))

end Subgroup
