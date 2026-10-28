module
public import CFSG.Quasithin.ChapterC.Section03.A5.PSL3Four

/-!
# The original alternating-five block excludes a PSL₃(4) overgroup

Restriction to the actual containing subgroup preserves both the block and
its literal elementary commutator layer. The intrinsic PSL₃(4) exclusion
therefore applies without changing the module or selecting a parabolic.
This is the PSL₃(4) alternative in Aschbacher–Smith 13.5.15, printed p.921;
construction and recognition of the source overgroup remain separate.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Source application to an original block and its actual containing group. -/
theorem no_psl3Four_subgroup_containing_alternatingFive
    (A X : Subgroup G) (hA : IsAlternatingBlock A 5) (hAX : A ≤ X)
    (hc : Nat.card ((blockU A).map A.subtype) = 16)
    (e : X ≃* Matrix.PSL3Four.PSL) : False := by
  let B := A.subgroupOf X
  let a : B ≃* A := subgroupOfEquivOfLe hAX
  have hB : IsAlternatingBlock B 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv a.symm hA
  have hU : (blockU B).map B.subtype = ((blockU A).map A.subtype).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hAX),
      ← RankOne.Solvable.blockU_map_equiv a,map_map,map_map]
    rfl
  apply no_alternatingFive_of_psl3Four_equiv e B hB
  rw [hU,Nat.card_congr (subgroupOfEquivOfLe ((map_subtype_le _).trans hAX)).toEquiv]
  exact hc

end CFSG.Quasithin.ChapterC
