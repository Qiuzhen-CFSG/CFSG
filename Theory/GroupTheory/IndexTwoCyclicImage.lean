module
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.IndexNormal
/-!
# A central involution in an index-two subgroup with cyclic image

If a subgroup has noncyclic structure but its image is cyclic, its kernel
is nontrivial. Faithfulness on an ambient index-two subgroup bounds this
kernel by two, so its nonidentity element is central and supplements the
intersection. This is the short complement argument used in the original
single-linear source 2.4.24(3); it requires no classification of two-groups.
-/
public section
open Subgroup
namespace Subgroup
variable {P H : Type*} [Group P] [Finite P] [Group H] [IsCyclic H]
theorem exists_central_involution_of_index_two_cyclic_image
    (S A : Subgroup P) (hi : S.index = 2) (hA : ¬ IsCyclic A)
    (f : P →* H) (hfaith : ∀ a ∈ A, a ∈ S → f a = 1 → a = 1) :
    ∃ x ∈ A, x ∉ S ∧ orderOf x = 2 ∧ f x = 1 ∧
      (∀ a ∈ A, Commute x a) ∧ A = zpowers x ⊔ (A ⊓ S) := by
  let : S.Normal := normal_of_index_eq_two hi
  let e := f.comp A.subtype
  let E := e.ker
  let q : E →* P ⧸ S := (QuotientGroup.mk' S).comp (A.subtype.comp E.subtype)
  have hq : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    exact hfaith a a.val.property ((QuotientGroup.eq_one_iff _).mp ha) a.property
  have hcard : Nat.card E ≤ 2 := by
    have hh := Nat.card_le_card_of_injective q hq
    change Nat.card E ≤ S.index at hh
    exact hi ▸ hh
  have hne : E ≠ ⊥ := by
    intro he
    exact hA (isCyclic_of_injective e (e.ker_eq_bot_iff.mp he))
  have htwo : Nat.card E = 2 := by
    have hp : 0 < Nat.card E := Nat.card_pos
    have hn : Nat.card E ≠ 1 := fun he => hne (E.card_eq_one.mp he)
    omega
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 (by rw [htwo])
  have hxP : orderOf ((x:A):P) = 2 := (orderOf_coe (x:A)).trans ((orderOf_coe x).trans hx)
  have hxS : ((x:A):P) ∉ S := by
    intro hs
    have he := hfaith x x.val.property hs x.property
    rw [he,orderOf_one] at hxP
    omega
  refine ⟨x,x.val.property,hxS,hxP,x.property,?_,?_⟩
  · intro a ha
    have he := mem_center_iff.mp (central_of_normal_card_two E htwo x.property) (⟨a,ha⟩:A)
    exact (congrArg Subtype.val he).symm
  · apply le_antisymm
    · intro a ha
      by_cases hs : a ∈ S
      · exact mem_sup_right ⟨ha,hs⟩
      · have hb : ((x:A):P)⁻¹*a ∈ A ⊓ S := ⟨A.mul_mem (A.inv_mem x.val.property) ha,
          (S.mul_mem_iff_of_index_two hi).mpr (by simpa only [inv_mem_iff] using iff_of_false hxS hs)⟩
        have hh := (zpowers ((x:A):P) ⊔ (A ⊓ S)).mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right hb)
        simpa only [mul_inv_cancel_left] using hh
    · exact sup_le (zpowers_le.mpr x.val.property) inf_le_left
end Subgroup
