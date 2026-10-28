module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The centralizer of a centerless normal subgroup

The centralizer of a normal subgroup with trivial center embeds in the
quotient by that subgroup. Consequently its order divides the subgroup
index. This transfers the prime exclusions on an outer quotient to its
centralizer, as used in Aschbacher--Smith D.3.21, printed pp.204--207.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A centerless normal subgroup has a centralizer whose order divides its index. -/
theorem centralizer_card_dvd_index_of_center_eq_bot
    (J : Subgroup G) [J.Normal] (hc : center J = ⊥) :
    Nat.card (centralizer (J : Set G)) ∣ J.index := by
  let C := centralizer (J : Set G)
  let f : C →* G ⧸ J := (QuotientGroup.mk' J).comp C.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    have hxJ : (x : G) ∈ J := (QuotientGroup.eq_one_iff _).mp hx
    have hxc : (⟨(x : G),hxJ⟩ : J) ∈ center J := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (x.property y y.property)
    have hxc' : (⟨(x : G),hxJ⟩ : J) ∈ (⊥ : Subgroup J) := hc ▸ hxc
    have hx1 : (x : G) = 1 := congrArg Subtype.val (mem_bot.mp hxc')
    exact mem_bot.mpr (Subtype.ext hx1)
  exact card_dvd_of_injective f hf

end Theory.GroupTheory
