module
public import Theory.GroupTheory.SelfCentralizingCoreCenter
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CoreCenter
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CharacteristicTwo
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization.NormalClosure

/-!
# Small core centers above the J₄ max2 and max4 two-cores

Every subgroup containing a self-centralizing normal p-subgroup has core
center embedded in that subgroup's center. Thus any overgroup of the max4
two-core has core center of order at most eight, without a normality
assumption on the overgroup.

For max2 the certified seed normal closure is self-centralizing and has
center of order two. Applying the same embedded-center argument first to
the local two-core bounds its center by two. The actual conjugating-word
equivalence transfers this to the original ATLAS max2 subgroup, and the
bound then passes to every overgroup of that subgroup's intrinsic two-core.
No ambient J₄ maximal-overgroup coverage is assumed or concluded.

Source: Aschbacher–Smith A.3.12(17), A.3.14(10) and 10.2.9; GLS3,
Table 5.3i. Literal ATLAS words and certificates are retained in the imports.
-/

public section
open Subgroup
namespace Janko4.LocalStructure
open OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData TwoCoreComparison.CoordinateGenerators

private theorem core_center_card_congr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : Nat.card (center (pCore 2 A)) = Nat.card (center (pCore 2 B)) := by
  let eP : pCore 2 A ≃* pCore 2 B :=
    (e.subgroupMap (pCore 2 A)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  exact Nat.card_congr (centerCongr eP).toEquiv

/-- The seed centralizer bound controls the core center in the conjugated max2 words. -/
theorem max2_local_twoCore_center_card_le_two :
    Nat.card (center (pCore 2 localSubgroup)) ≤ 2 := by
  have hQ : localNormalClosure ≤ pCore 2 localSubgroup :=
    le_sSup ⟨localNormalClosure_normal, localNormalClosure_isPGroup⟩
  have hC : centralizer (localNormalClosure : Set localSubgroup) ≤ localNormalClosure := by
    simpa only [localNormalClosureAction_ker] using localNormalClosureAction_ker_le
  exact (center_card_le_of_centralizer_le localNormalClosure (pCore 2 localSubgroup)
    hQ hC).trans_eq Realization.normalClosure_center_card

attribute [local irreducible] sourceSubgroupEquivLocal

/-- The center bound on the intrinsic core of the original ATLAS max2 subgroup. -/
theorem max2_twoCore_center_card_le_two :
    Nat.card (center (pCore 2 sourceSubgroup)) ≤ 2 := by
  have ht : Nat.card (center (pCore 2 sourceSubgroup)) =
      Nat.card (center (pCore 2 localSubgroup)) :=
    @core_center_card_congr sourceSubgroup localSubgroup inferInstance inferInstance
      sourceSubgroupEquivLocal
  exact ht.le.trans max2_local_twoCore_center_card_le_two

/-- Every overgroup of the original max2 core has core center of order at most two. -/
theorem max2_overgroup_twoCore_center_card_le_two
    (H : Subgroup sourceSubgroup) (hQ : pCore 2 sourceSubgroup ≤ H) :
    Nat.card (center (pCore 2 H)) ≤ 2 :=
  (center_pCore_card_le_of_pCore_le 2 H hQ max2_twoCore_centralizer_le).trans
    max2_twoCore_center_card_le_two

namespace SymmetricLinear
/-- Every overgroup of the actual max4 core has core center of order at most eight. -/
theorem overgroup_twoCore_center_card_le_eight
    (H : Subgroup max4Subgroup) (hQ : pCore 2 max4Subgroup ≤ H) :
    Nat.card (center (pCore 2 H)) ≤ 8 :=
  (center_pCore_card_le_of_pCore_le 2 H hQ max4_twoCore_centralizer_le).trans
    max4_twoCore_center_card_le_eight
end SymmetricLinear
end Janko4.LocalStructure
