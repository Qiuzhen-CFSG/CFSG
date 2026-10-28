module
public import Theory.SpecificGroups.AlternatingFiveInvolutionCover
public import Theory.GroupTheory.Commutator.PerfectQuotient

/-!
# Splitting a central double cover of A₅ with an involution lift

The kernel and derived subgroup generate a cover of the perfect group A₅.
If their intersection is nontrivial, the order-two kernel is contained in
the derived subgroup, making the entire cover perfect. The proved SL₂(5)
involution obstruction excludes this case when a noncentral involution
lifts. Thus the derived subgroup is an actual complement to the kernel.

Source application: DGS, Groups and Graphs (1985), the second splitting
in (5.16), p.117, as used in (10.9), p.163. No perfectness of the original
extension is assumed.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace alternatingGroup
/-- A central double cover of A₅ with a noncentral involution splits over its kernel. -/
theorem central_two_complement_of_involution
    {H : Type*} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center H) (hk : Nat.card f.ker = 2)
    (a : H) (ha : a ^ 2 = 1) (hne : f a ≠ 1) :
    f.ker.IsComplement' (commutator H) := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hgen := CentralExtension.ker_sup_commutator_eq_top_of_surjective f hf
  have hd : Disjoint f.ker (commutator H) := by
    let : Fact (Nat.card f.ker).Prime := ⟨hk ▸ Nat.prime_two⟩
    rcases ((commutator H).subgroupOf f.ker).eq_bot_or_eq_top_of_prime_card with he | he
    · apply disjoint_def.mpr
      intro x hx hy
      have hm : (⟨x,hx⟩ : f.ker) ∈ (commutator H).subgroupOf f.ker := hy
      rw [he,mem_bot] at hm
      exact congrArg Subtype.val hm
    · have hle : f.ker ≤ commutator H := fun x hx =>
        (show (⟨x,hx⟩ : f.ker) ∈ (commutator H).subgroupOf f.ker from he ▸ mem_top _)
      rw [sup_eq_right.mpr hle] at hgen
      let : Group.IsPerfect H := ⟨hgen⟩
      have hi := injective_of_central_two_kernel_of_involution f hf hc
        (IsPGroup.of_card (p := 2) (n := 1) hk) a ha hne
      have hb := (MonoidHom.ker_eq_bot_iff f).mpr hi
      rw [hb,card_bot] at hk
      omega
  apply isComplement'_of_disjoint_and_mul_eq_univ hd
  rw [←coe_mul_of_right_le_normalizer_left _ _ le_normalizer_of_normal,hgen]
  rfl
end alternatingGroup

