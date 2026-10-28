module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.Certificate
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Checks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Seeds

/-!
# Stage-one positive Schreier table: assembly

The representatives are the inverse positive words in the explicit 28160-vertex
tree. Its combinatorial facts, all tree-factor identities, and the two exact
stage-two generator seeds are certified. Incoming tree point images and the
remaining full-degree Schreier memberships are still required.

`stageOneTable_of_certificates` constructs the precise positive table from
those two independent inputs; its reduction is applied to the literal model
stages below. This is not an unconditional `stageOneTable` or stabilizer theorem.

Source: ATLAS F24G1-p306936B0 and GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo

/-- Assemble the actual word table once its point checks and nontree factors are proved. -/
def stageOneTable_of_certificates (ha : StageOne.TreeAction) (he : StageOne.RemainingEdges) :
    PositiveTable 1 (Fin 28160) where
  representative := StageOne.representative
  initial := StageOne.root
  initial_eq := StageOne.root_representative
  step a j := ⟨StageOne.prev a j,
    ⟨StageOne.schreier a (StageOne.prev a j),
      StageOne.all_edges_of_nonTree (StageOne.nonTreeEdges_of_remaining he)
        a (StageOne.prev a j)⟩,
    StageOne.positive_step a j⟩
  returns_base := StageOne.returns_base ha

/-- The table's reduction applies to the exact source-model stage and point. -/
theorem stage_one_reduction_of_certificates
    (ha : StageOne.TreeAction) (he : StageOne.RemainingEdges)
    (g : Equiv.Perm (Fin 306936)) (hg : g ∈ stage 1)
    (hfix : g (point 1) = point 1) : g ∈ stage 2 :=
  (stageOneTable_of_certificates ha he).reduction g hg hfix

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo
