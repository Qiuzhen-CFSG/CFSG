module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.TableChecks.Block0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.TableChecks.Block1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.TableChecks.Block2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.TableChecks.Block3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.TableChecks.Block4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.TableChecks.Block5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.TableChecks.Block6

/-!
# Checked stage-one tree data

The seven bounded certificate modules establish inverse columns, the isolated
root label and all incoming edges. No group word is evaluated by these checks.
The subsequent `Checks` module applies them to the actual word representatives.
Source: `source/tree.json`, ATLAS F24G1-p306936B0; GLS3 Table 5.3v.
Regenerate with `source/emit_checks.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

theorem table_facts (j : Vertex) :
    (∀ a : Fin 2, prev a (next a j) = j ∧ next a (prev a j) = j) ∧
    (label j = label root → j = root) ∧
    (j ≠ root → next (letter j) (parent j) = j) := by
  have h : localTest j.val = true := by
    by_cases h0 : j.val < 4096
    · exact range0_checked j.val (by omega) h0
    by_cases h1 : j.val < 8192
    · exact range1_checked j.val (by omega) h1
    by_cases h2 : j.val < 12288
    · exact range2_checked j.val (by omega) h2
    by_cases h3 : j.val < 16384
    · exact range3_checked j.val (by omega) h3
    by_cases h4 : j.val < 20480
    · exact range4_checked j.val (by omega) h4
    by_cases h5 : j.val < 24576
    · exact range5_checked j.val (by omega) h5
    · exact range6_checked j.val (by omega) j.isLt
  simpa only [localTest, Nat.mod_eq_of_lt j.isLt, decide_eq_true_eq] using h

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne
