module
public import Theory.Representation.PSL3Two.NaturalDualNormalCore
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CoreOvergroupCenter

/-!
# J₄ rows excluded by the marked natural-dual core centre

A normal marked natural-dual module forces the centre of the full local
core to have at least 64 elements. The literal max2 and max4 cores have
centres of order at most two and eight. Transport through an actual local
group equivalence therefore excludes both rows. No coverage of arbitrary
maximal two-locals is asserted.

Source: the J₄ inspection in Aschbacher–Smith 4.4.3, printed pp.622–623;
the existing core certificates retain the literal ATLAS word subgroups.
-/

public section
namespace Janko4.LocalStructure.BinaryThreeModules
open Subgroup BinaryLinearThree.NaturalDual
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
variable {M : Type*} [Group M]

/-- A local with the marked six-space obstruction cannot be the literal max2 row. -/
theorem not_max2_of_core_center_large (h : 64 ≤ Nat.card (center (pCore 2 M))) :
    ¬ Nonempty (M ≃* sourceSubgroup) := by
  rintro ⟨e⟩
  rw [@core_center_card_congr M sourceSubgroup inferInstance inferInstance e] at h
  have hb := max2_twoCore_center_card_le_two
  omega

/-- The literal max4 row also has too small a full core centre. -/
theorem not_max4_of_core_center_large (h : 64 ≤ Nat.card (center (pCore 2 M))) :
    ¬ Nonempty (M ≃* SymmetricLinear.max4Subgroup) := by
  rintro ⟨e⟩
  rw [@core_center_card_congr M SymmetricLinear.max4Subgroup
    inferInstance inferInstance e] at h
  have hb := SymmetricLinear.max4_twoCore_center_card_le_eight
  omega
end Janko4.LocalStructure.BinaryThreeModules
