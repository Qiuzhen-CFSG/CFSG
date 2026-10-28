module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Reduction
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.PGroup.CriticalSubgroup

/-!
# The core centralizer and order used by the final source contradiction

The pair group YU has characteristic two because Y does and U is a
normalizing two-group. Consequently its two-core centralizer is exactly
the center already identified in 15.3.55. The already proved compatible LayerActions provide the remaining
order and module facts.

Source: Aschbacher–Smith, 15.3.54–55 and 15.3.59, printed pp.1146–1149.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
variable {G : Type*} [Group G]

theorem pair_core_centralizer_of_center (Y U V : Subgroup G)
    (hY : centralizer (pCore 2 Y : Set Y) ≤ pCore 2 Y)
    (hU : IsPGroup 2 U) (hn : U ≤ normalizer (Y : Set G))
    (hc : (center ((Y ⊔ U).pCoreIn 2)).map ((Y ⊔ U).pCoreIn 2).subtype = V) :
    (Y ⊔ U) ⊓ centralizer ((Y ⊔ U).pCoreIn 2 : Set G) = V := by
  have hself := (inf_centralizer_pCoreIn_le_iff 2 (Y ⊔ U)).mpr
    (centralizer_pCore_sup_le 2 Y U hY hU hn)
  rw [map_center_subtype_eq_inf_centralizer] at hc
  apply le_antisymm
  · exact (le_inf hself inf_le_right).trans_eq hc
  · rw [← hc]
    exact inf_le_inf_right _ (pCoreIn_le 2 (Y ⊔ U))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
