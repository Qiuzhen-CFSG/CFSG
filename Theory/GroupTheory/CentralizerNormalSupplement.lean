module
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers in a centerless normal supplement

If a centerless normal subgroup and a Sylow two-subgroup generate a group,
the normal subgroup's centralizer embeds in the two-group quotient. It is
therefore a normal two-subgroup and lies in the specified Sylow subgroup.
This is the centralizer step in Aschbacher--Smith 2.5.8(2), p.556.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G]
/-- The centralizer of the normal centerless factor lies in the Sylow supplement. -/
theorem centralizer_le_sylow_of_normal_centerless_sup
    (K : Subgroup G) [K.Normal] (S : Sylow 2 G)
    (hz : center K = ⊥) (hgen : K ⊔ (S : Subgroup G) = ⊤) :
    centralizer (K : Set G) ≤ S := by
  let C := centralizer (K : Set G)
  let f : C →* G ⧸ K := (QuotientGroup.mk' K).comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff _).mp hx
    have hxc : (⟨x,hxK⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (x.property k k.property)
    rw [hz] at hxc
    have hx1 : (x : G) = 1 := congrArg (fun k : K => (k : G)) (mem_bot.mp hxc)
    exact mem_bot.mpr (Subtype.ext hx1)
  have hp : IsPGroup 2 C :=
    (isPGroup_quotient_of_sup_eq_top K S S.isPGroup' hgen).of_injective f hf
  exact hp.le_sylow_of_normal S
end Theory.GroupTheory
