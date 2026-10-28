module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Setup

/-!
# Six literal Schreier seeds

The original word witnesses for the proposed next groups are exactly six
nontree edges of these right-coset tables. Their membership follows from
the defining generator lists in any group, with no action comparison or
stabilizer recognition. These are initial facts for a Schreier membership
certificate, not a proof that all nontree edges lie in the next group.
Source: shared `source/faithfulness/nodes.json`, ATLAS F24G1-p306936B0.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour

local instance (i : Fin 2) : NeZero (size i) := ⟨Nat.ne_of_gt (size_pos i)⟩

private theorem g00 : gen 0 0 = Word.word11 aPerm bPerm := rfl
private theorem g01 : gen 0 1 = Word.word14 aPerm bPerm := rfl
private theorem g10 : gen 1 0 = Word.word17 aPerm bPerm := rfl
private theorem g11 : gen 1 1 = Word.word20 aPerm bPerm := rfl

theorem seed17_eq : schreier 0 0 3093 = Word.word17 aPerm bPerm := by
  have hj : repWord 0 3093 = [0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0] := by decide +kernel
  have hk : repWord 0 170 = [0, 1, 0, 1, 1, 0, 1] := by decide +kernel
  have hn : next 0 0 3093 = 170 := by decide +kernel
  simp only [schreier, hn, representative, hj, hk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, g00, g01,
    Word.word17, Word.word15, Word.word16, mul_assoc]

theorem seed17_mem : schreier 0 0 3093 ∈ stage 3 := by
  rw [seed17_eq]
  apply Subgroup.subset_closure
  simp [Word.generators]

theorem seed20_eq : schreier 0 0 2608 = Word.word20 aPerm bPerm := by
  have hj : repWord 0 2608 = [0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0] := by decide +kernel
  have hk : repWord 0 2909 = [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] := by decide +kernel
  have hn : next 0 0 2608 = 2909 := by decide +kernel
  simp only [schreier, hn, representative, hj, hk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, g00, g01,
    Word.word20, Word.word18, Word.word19, mul_assoc]

theorem seed20_mem : schreier 0 0 2608 ∈ stage 3 := by
  rw [seed20_eq]
  apply Subgroup.subset_closure
  simp [Word.generators]

theorem seed23_eq : schreier 1 0 586 = Word.word23 aPerm bPerm := by
  have hj : repWord 1 586 = [1, 1, 1, 1, 1, 1, 1, 0, 0, 0] := by decide +kernel
  have hk : repWord 1 619 = [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1] := by decide +kernel
  have hn : next 1 0 586 = 619 := by decide +kernel
  simp only [schreier, hn, representative, hj, hk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, g10, g11,
    Word.word23, Word.word21, Word.word22, mul_assoc]

theorem seed23_mem : schreier 1 0 586 ∈ stage 4 := by
  rw [seed23_eq]
  apply Subgroup.subset_closure
  simp [Word.generators]

theorem seed26_eq : schreier 1 0 494 = Word.word26 aPerm bPerm := by
  have hj : repWord 1 494 = [0, 0, 0, 1, 1, 1, 0, 1, 1, 1] := by decide +kernel
  have hk : repWord 1 73 = [0, 1, 0, 0, 0, 1] := by decide +kernel
  have hn : next 1 0 494 = 73 := by decide +kernel
  simp only [schreier, hn, representative, hj, hk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, g10, g11,
    Word.word26, Word.word24, Word.word25, mul_assoc]

theorem seed26_mem : schreier 1 0 494 ∈ stage 4 := by
  rw [seed26_eq]
  apply Subgroup.subset_closure
  simp [Word.generators]

theorem seed29_eq : schreier 1 1 328 = Word.word29 aPerm bPerm := by
  have hj : repWord 1 328 = [0, 0, 0, 1, 0, 0, 1, 0, 1] := by decide +kernel
  have hk : repWord 1 358 = [0, 0, 1, 1, 0, 0, 1, 0, 0] := by decide +kernel
  have hn : next 1 1 328 = 358 := by decide +kernel
  simp only [schreier, hn, representative, hj, hk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, g10, g11,
    Word.word29, Word.word27, Word.word28, mul_assoc]

theorem seed29_mem : schreier 1 1 328 ∈ stage 4 := by
  rw [seed29_eq]
  apply Subgroup.subset_closure
  simp [Word.generators]

theorem seed32_eq : schreier 1 0 399 = Word.word32 aPerm bPerm := by
  have hj : repWord 1 399 = [0, 1, 1, 0, 0, 1, 0, 1, 0] := by decide +kernel
  have hk : repWord 1 92 = [1, 0, 1, 0, 1, 1] := by decide +kernel
  have hn : next 1 0 399 = 92 := by decide +kernel
  simp only [schreier, hn, representative, hj, hk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, g10, g11,
    Word.word32, Word.word30, Word.word31, mul_assoc]

theorem seed32_mem : schreier 1 0 399 ∈ stage 4 := by
  rw [seed32_eq]
  apply Subgroup.subset_closure
  simp [Word.generators]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour
