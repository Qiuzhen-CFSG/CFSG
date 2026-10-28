module

public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Faithfulness detected on a normal subgroup

If a homomorphism is faithful on a normal subgroup, its kernel centralizes
that subgroup: their commutator lies in their trivial intersection. Thus a
trivial normal-subgroup centralizer makes the whole homomorphism faithful.
The inclusion form applies to representations of an intermediate subgroup
without replacing its literal inclusion maps.

This is the elementary kernel argument in the normal-constituent passage of
Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.42 and D.3.9.
-/

public section
open Subgroup
namespace MonoidHom
variable {G M : Type*} [Group G] [Monoid M]

/-- A kernel that is trivial on a normal subgroup centralizes that subgroup. -/
theorem ker_le_centralizer_of_injective_normal_restriction
    (f : G →* M) (N : Subgroup G) [N.Normal]
    (hi : Function.Injective (f.comp N.subtype)) :
    f.ker ≤ centralizer (N : Set G) := by
  have hinf : f.ker ⊓ N = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have he : (⟨x, hx.2⟩ : N) = 1 :=
      hi (by change f x = f 1; rw [map_one]; exact hx.1)
    exact congrArg Subtype.val he
  exact commutator_eq_bot_iff_le_centralizer.mp
    (le_bot_iff.mp ((commutator_le_inf _ _).trans hinf.le))

/-- Faithfulness on a normal subgroup with trivial centralizer implies
faithfulness on the whole group. The target may be the endomorphism monoid
of a representation. -/
theorem injective_of_injective_normal_restriction
    (f : G →* M) (N : Subgroup G) [N.Normal]
    (hi : Function.Injective (f.comp N.subtype))
    (hc : centralizer (N : Set G) = ⊥) : Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  exact le_bot_iff.mp
    ((ker_le_centralizer_of_injective_normal_restriction f N hi).trans hc.le)

/-- The same criterion for the literal inclusion of the normal subgroup
into any intermediate actor group. -/
theorem injective_of_injective_normal_inclusion
    (N H : Subgroup G) [N.Normal] (hNH : N ≤ H)
    (f : H →* M) (hi : Function.Injective (f.comp (inclusion hNH)))
    (hc : centralizer (N : Set G) = ⊥) : Function.Injective f := by
  have hi' : Function.Injective (f.comp (N.subgroupOf H).subtype) :=
    hi.comp (subgroupOfEquivOfLe hNH).injective
  apply injective_of_injective_normal_restriction f (N.subgroupOf H) hi'
  apply le_bot_iff.mp
  intro x hx
  have hxG : (x : G) ∈ centralizer (N : Set G) := by
    intro n hn
    exact congrArg Subtype.val (hx ⟨n, hNH hn⟩ hn)
  apply Subtype.ext
  exact mem_bot.mp (hc ▸ hxG)

end MonoidHom
