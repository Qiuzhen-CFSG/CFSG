module

public import Theory.GroupTheory.QuaternionSwapModel.MarkedSylow.Thompson
public import Theory.GroupTheory.UniqueElementarySubgroups

/-!
# The unique elementary sixteen in the marked quaternion Sylow

The checked whole-Sylow census puts every elementary sixteen inside the
displayed sixteen. Equality of orders gives uniqueness as an actual
subgroup of the marked Sylow group. Source: Aschbacher–Smith 14.2.21.
-/

public section
open Subgroup
namespace QuaternionSwapModel.MarkedSylow.Geometry
open QuaternionSwapModel
variable {G : Type*} [Group G] [Finite G] {f : QH →* G} {T : Subgroup G}

theorem existsUnique_elementary_sixteen (d : Geometry f T) :
    ∃! E : Subgroup T, IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  let B := A.map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hB : B ≤ T := d.A_le
  have hcB : Nat.card B = 16 := (card_map_of_injective d.injective).trans card_A
  have hc : Nat.card (B.subgroupOf T) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv).trans hcB
  refine ⟨B.subgroupOf T, ⟨IsElementaryAbelian.subgroupOf hB, hc⟩, ?_⟩
  intro E hE
  let := hE.1
  have hec : Nat.card (E.map T.subtype) = 16 :=
    (card_map_of_injective T.subtype_injective).trans hE.2
  let : IsElementaryAbelian 2 (E.map T.subtype) := IsElementaryAbelian.map _
  have hl := d.large_elementary_le (E.map T.subtype) (map_subtype_le E) hec.ge
  apply eq_of_le_of_card_ge
  · intro x hx
    exact hl (mem_map.mpr ⟨x,hx,rfl⟩)
  · exact hc.trans hE.2.symm |>.le
end QuaternionSwapModel.MarkedSylow.Geometry
