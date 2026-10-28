module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PCoreImage

/-!
# Restricting an ambient local two-core

For A≤H, the two-core of A restricted to H is the literal restriction of
its ambient two-core. This
identity keeps the ambient and intrinsic maps explicit in I.5.7.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

theorem pCoreIn_subgroupOf (p : ℕ) (A H : Subgroup G) (hAH : A ≤ H) :
    (A.subgroupOf H).pCoreIn p = (A.pCoreIn p).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [map_subgroupOf_eq_of_le ((A.pCoreIn_le p).trans hAH)]
  let e : A.subgroupOf H ≃* A := subgroupOfEquivOfLe hAH
  have hcomp : H.subtype.comp (A.subgroupOf H).subtype = A.subtype.comp e.toMonoidHom := rfl
  rw [pCoreIn, map_map, hcomp, ← map_map, pCore_map_iso]
  rfl

end Subgroup
