module
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# Centralizing an action preserves its kernel-containing local subgroups

Let Q≤S normalize R and contain C_S(R). If x normalizes S and centralizes
R, then conjugation by x fixes Q modulo C_S(R), hence normalizes Q.
No assumption that x normalizes a larger component is needed.
This is the crossing calculation in Aschbacher--Smith 2.5.15, p.559.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] {S R Q : Subgroup G} {x : G}

theorem mem_normalizer_of_centralizes_action_kernel
    (hQS : Q ≤ S) (hQN : Q ≤ normalizer (R : Set G))
    (hC : S ⊓ centralizer (R : Set G) ≤ Q)
    (hxS : x ∈ normalizer (S : Set G))
    (hxR : x ∈ centralizer (R : Set G)) : x ∈ normalizer (Q : Set G) := by
  have hforward (a : G) (haS : a ∈ normalizer (S : Set G))
      (haR : a ∈ centralizer (R : Set G)) (q : G) (hq : q ∈ Q) : a*q*a⁻¹ ∈ Q := by
    have haqS : a*q*a⁻¹ ∈ S := (haS q).mp (hQS hq)
    let N := normalizer (R : Set G)
    let aa : N := ⟨a,centralizer_le_normalizer _ haR⟩
    let qq : N := ⟨q,hQN hq⟩
    have ha : R.normalizerMonoidHom aa = 1 := by
      rw [← MonoidHom.mem_ker,normalizerMonoidHom_ker]
      exact haR
    have hk : qq⁻¹*(aa*qq*aa⁻¹) ∈ R.normalizerMonoidHom.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul,map_inv,map_mul,map_mul,map_inv,ha]
      simp only [one_mul,mul_one,inv_one,inv_mul_cancel]
    rw [normalizerMonoidHom_ker] at hk
    have hh := Q.mul_mem hq (hC ⟨S.mul_mem (S.inv_mem (hQS hq)) haqS,hk⟩)
    simpa only [mul_inv_cancel_left] using hh
  change ∀ q : G, q ∈ Q ↔ x*q*x⁻¹ ∈ Q
  intro q
  constructor
  · exact hforward x hxS hxR q
  · intro hq
    have hh := hforward x⁻¹ ((normalizer (S : Set G)).inv_mem hxS)
      ((centralizer (R : Set G)).inv_mem hxR) (x*q*x⁻¹) hq
    simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hh
end Subgroup
