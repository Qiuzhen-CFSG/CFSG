module

public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.WeaklyClosedInvolutionSimple
public import Theory.GroupTheory.OrderFourTransfer
public import Theory.GroupTheory.InvolutionTransfer

/-!
# Fusion constraints for the Held centralizer splitting problem

Under the original finite simple ambient-group hypotheses, the distinguished
involution is noncentral and has a distinct conjugate in the chosen Sylow
subgroup. The ambient group is perfect and has no normal subgroup of index
two. Consequently Thompson transfer supplies involution fusion into every
index-two Sylow subgroup, and order-four fusion into binary-character kernels
when the character kills all involutions.

The centralizer order bounds the ambient order by 384, excluding the cyclic
simple case. Simplicity and the checked core-free Z-star theorem then give
the distinct conjugate. The transfer statements use the actual Sylow inclusion
in the ambient group. These are necessary conditions for the nonsplit-case
exclusion; they do not assert that the elementary kernel has a complement.

Source for the splitting problem: Huppert--Blackburn, *Finite Groups III*,
XII.1.18(b), printed p.314; D. Held, J. Algebra 8 (1968), 436--449,
DOI 10.1016/0021-8693(68)90054-9. The fusion tools are Glauberman's Z-star
and Thompson transfer, proved in the imported modules.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.LocalData
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)

omit [IsSimpleGroup G] in
/-- The actual involution centralizer supplies a lower bound for the ambient order. -/
public theorem ambient_card_lower_bound (D : LocalData G) : 384 ≤ Nat.card G := by
  rw [← D.centralizer_card]
  exact Nat.card_le_card_of_injective _ D.centralizer.subtype_injective

/-- The centralizer involution is noncentral in the simple ambient group. -/
public theorem z_not_mem_ambient_center : D.z ∉ center G := by
  intro hz
  let N := zpowers D.z
  have hNC : N ≤ center G := zpowers_le.mpr hz
  have hN : N.Normal := ⟨fun n hn g => by
    rw [mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp (hNC hn) g)]
    exact hn⟩
  rcases hN.eq_bot_or_eq_top with hb | ht
  · have he : D.z ∈ (⊥ : Subgroup G) := hb ▸ mem_zpowers D.z
    exact D.z_ne_one he
  · have he : Nat.card G = 2 := by
      rw [← Subgroup.card_top (G := G), ← ht]
      exact (Nat.card_zpowers D.z).trans D.z_order
    have := ambient_card_lower_bound D
    omega

/-- Z-star forces a second ambient conjugate in the chosen Sylow subgroup. -/
public theorem exists_distinct_sylow_conjugate : ∃ t : D.sylow,
    t ≠ (D.involution : D.sylow) ∧ IsConj D.z (t : G) := by
  by_contra! h
  apply z_not_mem_ambient_center D
  apply D.sylow.weakly_closed_involution_mem_center_of_simple
    (D.involution : D.sylow) _ D.involution.property
  · intro t ht
    by_contra hne
    exact h t hne ht
  · exact (Subgroup.orderOf_coe D.involution).trans D.involution_order

/-- The ambient simple group has no normal subgroup of index two. -/
public theorem no_normal_index_two (D : LocalData G) (N : Subgroup G) (hN : N.Normal) : N.index ≠ 2 := by
  rcases hN.eq_bot_or_eq_top with rfl | rfl
  · rw [Subgroup.index_bot]
    have := ambient_card_lower_bound D
    omega
  · simp

/-- Every Sylow involution has an ambient conjugate in every index-two subgroup. -/
public theorem involution_conjugate_mem_index_two (U : Subgroup D.sylow) (hU : U.index = 2)
    (t : D.sylow) (ht : orderOf t = 2) :
    ∃ u : D.sylow, IsConj (t : G) (u : G) ∧ u ∈ U :=
  D.sylow.exists_isConj_mem_of_index_two (no_normal_index_two D) U hU t ht

/-- Transfer forces order-four fusion into a character kernel killing involutions. -/
public theorem order_four_conjugate_mem_character_kernel {A : Type*} [CommGroup A] [Finite A]
    (χ : D.sylow →* A) (hA : Nat.card A = 2)
    (hinv : ∀ t : D.sylow, t ^ 2 = 1 → χ t = 1)
    (t : D.sylow) (ht : orderOf t = 4) :
    ∃ u : D.sylow, IsConj (t : G) (u : G) ∧ χ u = 1 :=
  D.sylow.exists_isConj_ker_of_order_four (no_normal_index_two D) χ hA hinv t ht

/-- The original hypotheses force the ambient group to be perfect. -/
public theorem ambient_commutator_eq_top (D : LocalData G) : _root_.commutator G = ⊤ := by
  rcases (inferInstance : (_root_.commutator G).Normal).eq_bot_or_eq_top with hb | ht
  · apply (z_not_mem_ambient_center D).elim
    apply mem_center_iff.mpr
    intro x
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hm := Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
      (Subgroup.mem_top D.z)
    rwa [← commutator_def, hb, mem_bot] at hm
  · exact ht

/-- The cyclic simple case is excluded by the original local hypotheses. -/
public theorem ambient_not_isSolvable (D : LocalData G) : ¬ Group.IsSolvable G := by
  intro hs
  let := hs
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne (ambient_commutator_eq_top D)
end Theory.GroupTheory.HeldM22A10.LocalData
