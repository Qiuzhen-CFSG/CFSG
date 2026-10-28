module
public import Theory.GroupTheory.CComponent.SimplePairKernel
public import Theory.GroupTheory.SolvableRadical

/-!
# The radical of a pair of simple-core C-components

The solvable radical cannot contain a C-component. For two distinct
C-components with simple quotients by their two-cores, the component-pair
kernel theorem therefore makes the radical of their join a two-group.
All component assumptions are relative to the specified ambient group.

Source: standard component calculus, applied in Aschbacher--Smith
15.2.12(2) and 15.2.23, printed pp.1111 and 1116.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A pair of distinct C-components with simple two-core quotients has
two-group solvable radical. -/
theorem radical_isTwoGroup_of_simple_core_pair (A B : Subgroup G)
    (hA : A.IsCComponent) (hB : B.IsCComponent) (hne : A ≠ B)
    [IsSimpleGroup (A ⧸ pCore 2 A)] [IsSimpleGroup (B ⧸ pCore 2 B)] :
    IsPGroup 2 (solvableRadical (A ⊔ B : Subgroup G)) := by
  let U := A ⊔ B
  let A' := A.subgroupOf U
  let B' := B.subgroupOf U
  have ha : A ≤ U := le_sup_left
  have hb : B ≤ U := le_sup_right
  let ea := subgroupOfEquivOfLe ha
  let eb := subgroupOfEquivOfLe hb
  let : IsSimpleGroup (A' ⧸ pCore 2 A') :=
    (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).isSimpleGroup
  let : IsSimpleGroup (B' ⧸ pCore 2 B') :=
    (QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)).isSimpleGroup
  have hg : A' ⊔ B' = ⊤ := by
    rw [← subgroupOf_sup ha hb, subgroupOf_self]
  let : (A' ⊔ B').Normal := hg ▸ inferInstance
  refine isTwoGroup_of_normal_avoiding_simpleCore_pair A' B' ⊥ (solvableRadical U)
    (hA.subgroupOf ha) (hB.subgroupOf hb) ?_ IsPGroup.of_bot (by rw [hg, sup_bot_eq]) ?_ ?_
  · intro he
    apply hne
    have hm := congrArg (map U.subtype) he
    simpa only [A',B',map_subgroupOf_eq_of_le ha,map_subgroupOf_eq_of_le hb] using hm
  · intro hle
    exact (hA.subgroupOf ha).not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := inclusion hle) (inclusion_injective hle))
  · intro hle
    exact (hB.subgroupOf hb).not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := inclusion hle) (inclusion_injective hle))

end Theory.GroupTheory
