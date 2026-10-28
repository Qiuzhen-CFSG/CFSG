module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Setup

/-!
# Two actual stage-one Schreier seeds

These two edges are the literal defining generators of stage two. Their
identities are word algebra in the full ambient symmetric group; no smaller
orbit comparison or numerical order supplies the membership proof.
They are seeds for the remaining nontree membership certificate.

Source: `source/faithfulness/nodes.json`, ATLAS F24G1-p306936B0; GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

private theorem g0 : gen 0 = Word.word5 aPerm bPerm := rfl
private theorem g1 : gen 1 = Word.word8 aPerm bPerm := rfl

theorem seed11_eq : schreier 0 23760 = Word.word11 aPerm bPerm := by
  have hj : repWord 23760 = [1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] := by decide +kernel
  have hk : repWord 23213 = [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1] := by decide +kernel
  have hn : next 0 23760 = 23213 := by decide +kernel
  simp only [schreier, hn, rightRep, hj, hk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, g0, g1,
    Word.word11, Word.word9, Word.word10, mul_assoc]

theorem seed11_mem : schreier 0 23760 ∈ stage 2 := by
  rw [seed11_eq]
  apply Subgroup.subset_closure
  simp [Word.generators]

theorem seed14_eq : schreier 1 6558 = Word.word14 aPerm bPerm := by
  have hj : repWord 6558 = [1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0] := by decide +kernel
  have hk : repWord 9857 = [0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0] := by decide +kernel
  have hn : next 1 6558 = 9857 := by decide +kernel
  simp only [schreier, hn, rightRep, hj, hk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, g0, g1,
    Word.word14, Word.word12, Word.word13, mul_assoc]

theorem seed14_mem : schreier 1 6558 ∈ stage 2 := by
  rw [seed14_eq]
  apply Subgroup.subset_closure
  simp [Word.generators]

/-- Only nontree edges other than the two defining generators remain. -/
def RemainingEdges : Prop :=
  ∀ (a : Fin 2) (j : Vertex), ¬ IsTree a j →
    (a, j) ≠ (0, 23760) → (a, j) ≠ (1, 6558) → schreier a j ∈ stage 2

/-- Insert the two certified source-word seeds into the nontree certificate. -/
theorem nonTreeEdges_of_remaining (he : RemainingEdges) : NonTreeEdges := by
  intro a j ht
  by_cases h₀ : (a, j) = (0, 23760)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₀
    exact seed11_mem
  by_cases h₁ : (a, j) = (1, 6558)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁
    exact seed14_mem
  exact he a j ht h₀ h₁

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne
