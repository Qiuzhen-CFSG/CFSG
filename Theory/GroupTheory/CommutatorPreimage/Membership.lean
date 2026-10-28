module
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Elementwise membership in a commutator preimage

The subgroup centralizing an actor modulo a normalized layer consists exactly
of the elements whose commutators with every actor lie in that layer.
-/
public section
namespace Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem mem_commutatorPreimage_iff (Q E Z : Subgroup G)
    (hQZ : Q ≤ normalizer (Z : Set G)) (x : G) :
    x ∈ commutatorPreimage Q E Z ↔ x ∈ Q ∧ ∀ e ∈ E, ⁅x,e⁆ ∈ Z := by
  let K : Subgroup G := {
    carrier := {x | x ∈ Q ∧ ∀ e ∈ E, ⁅x,e⁆ ∈ Z}
    one_mem' := ⟨Q.one_mem, by simp⟩
    mul_mem' := by
      rintro a b ⟨ha,hac⟩ ⟨hb,hbc⟩
      refine ⟨Q.mul_mem ha hb, fun e he => ?_⟩
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact Z.mul_mem (le_normalizer_iff.mp hQZ a ha _ (hbc e he)) (hac e he)
    inv_mem' := by
      rintro a ⟨ha,hac⟩
      refine ⟨Q.inv_mem ha, fun e he => ?_⟩
      rw [commutatorElement_inv_left]
      have hh : ⁅e,a⁆ ∈ Z := by
        rw [← commutatorElement_inv]
        exact Z.inv_mem (hac e he)
      simpa only [inv_inv] using
        le_normalizer_iff.mp hQZ a⁻¹ (Q.inv_mem ha) _ hh }
  constructor
  · intro hx
    exact ⟨commutatorPreimage_le Q E Z hx, fun e he =>
      commutator_commutatorPreimage_le Q E Z hQZ (commutator_mem_commutator hx he)⟩
  · intro hx
    have hK : K ≤ commutatorPreimage Q E Z := le_commutatorPreimage
      (fun _ ha => ha.1) (commutator_le.mpr fun a ha => ha.2)
    exact hK hx
end Subgroup
