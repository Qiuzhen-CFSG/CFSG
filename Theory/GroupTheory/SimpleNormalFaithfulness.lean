module
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Faithfulness detected on a simple normal subgroup

For a homomorphism out of a group with a normal subgroup B, injectivity
on B makes the kernel disjoint from B and hence centralize B. The kernel
also embeds in the quotient by B. If the centralizer order and index of B
are coprime, the kernel is trivial. For simple B, nontriviality of the
restriction suffices. This applies to finite almost-simple actions without
requiring a classification of the ambient normal subgroups.

Source application: Aschbacher--Smith, 11.1.2, printed pp.763--764,
the action on the selected KX-chief section.
-/

public section
open Subgroup
namespace MonoidHom
variable {G M : Type*} [Group G] [Monoid M]

/-- An injective normal restriction detects faithfulness when the centralizer
order is coprime to the normal subgroup index. -/
theorem injective_of_normal_restriction_coprime (f : G →* M)
    (B : Subgroup G) [B.Normal]
    (hB : Function.Injective (f.comp B.subtype))
    (hcop : Nat.Coprime (Nat.card (centralizer (B : Set G))) B.index) :
    Function.Injective f := by
  have hd : Disjoint f.ker B := by
    apply disjoint_def.mpr
    intro x hx hxb
    have he : (⟨x,hxb⟩ : B) = 1 := hB (hx.trans (map_one f).symm)
    exact congrArg Subtype.val he
  have hc : f.ker ≤ centralizer (B : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
  let q := QuotientGroup.mk' B
  have hq : Function.Injective (q.comp f.ker.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact hd.le_bot ⟨x.property, (QuotientGroup.eq_one_iff (x : G)).mp hx⟩
  have hi : Nat.card f.ker ∣ B.index := by
    rw [index_eq_card]
    exact card_dvd_of_injective _ hq
  apply (MonoidHom.ker_eq_bot_iff f).mp
  exact Subgroup.card_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop (card_dvd_of_le hc) hi)

/-- A nontrivial action on the simple normal subgroup detects faithfulness. -/
theorem injective_of_simple_normal_moved (f : G →* M)
    (B : Subgroup G) [B.Normal] [IsSimpleGroup B]
    (hm : ∃ b : B, f b ≠ 1)
    (hcop : Nat.Coprime (Nat.card (centralizer (B : Set G))) B.index) :
    Function.Injective f := by
  apply injective_of_normal_restriction_coprime f B ?_ hcop
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.comp B.subtype).ker inferInstance with h | h
  · exact h
  · obtain ⟨b,hb⟩ := hm
    exact (hb (h.ge (mem_top b))).elim
end MonoidHom
