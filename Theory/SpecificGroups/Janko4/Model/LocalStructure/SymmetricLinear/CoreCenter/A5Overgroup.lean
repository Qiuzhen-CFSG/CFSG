module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CoreCenter
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.A5Factor
/-!
# Core centers in marked overgroups of the J₄ max4 core

A normal overgroup of the actual max4 two-core has an isomorphic two-core.
The bound of eight for its center therefore transfers to every such marked
local, including the literal A₅-factor preimage.

Source context: Aschbacher–Smith A.3.14(10) and source 10.2.9.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear
open Subgroup
/-- Every normal overgroup of the max4 two-core has core center of order at most eight. -/
theorem normal_overgroup_twoCore_center_card_le_eight
    (H : Subgroup max4Subgroup) [H.Normal] (hQ : pCore 2 max4Subgroup ≤ H) :
    Nat.card (center (pCore 2 H)) ≤ 8 := by
  let ec : center (pCore 2 H) ≃* center (pCore 2 max4Subgroup) :=
    centerCongr (normalOvergroupCoreEquiv H hQ)
  have ht : Nat.card (center (pCore 2 H)) = Nat.card (center (pCore 2 max4Subgroup)) :=
    Nat.card_congr ec.toEquiv
  rw [ht]
  exact max4_twoCore_center_card_le_eight
end Janko4.LocalStructure.SymmetricLinear
