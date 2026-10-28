module
public import Mathlib.GroupTheory.Nilpotent

/-!
# Pulling back upper central series along an embedding

If a group embeds in another, the inverse image of every upper central
term lies in the corresponding term of the subgroup. Induction uses
injectivity at the zero term and preservation of commutators thereafter.
The source application restricts the actual middle's second center to its
first core in the J.4.5 binary Ree calculation.
-/

public section
open scoped commutatorElement
namespace Subgroup
theorem comap_upperCentralSeries_le_of_injective {H K:Type*} [Group H] [Group K]
    (f:H→*K) (hf:Function.Injective f) : ∀n:ℕ,
    (Subgroup.upperCentralSeries K n).comap f≤Subgroup.upperCentralSeries H n
  | 0 => by
      rw [Subgroup.upperCentralSeries_zero,Subgroup.upperCentralSeries_zero,MonoidHom.comap_bot,
        (MonoidHom.ker_eq_bot_iff f).mpr hf]
  | n+1 => by
      intro x hx
      apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
      intro y
      apply comap_upperCentralSeries_le_of_injective f hf n
      change f ⁅x,y⁆∈Subgroup.upperCentralSeries K n
      rw [map_commutatorElement]
      exact Subgroup.mem_upperCentralSeries_succ_iff.mp hx (f y)


end Subgroup
