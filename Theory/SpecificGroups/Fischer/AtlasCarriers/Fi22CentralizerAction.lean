module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22
public import Theory.GroupAction.CentralizerFixedPoints

/-!
# The fixed-point action of the ATLAS Fi22 centralizer

We use the first published generator and restrict its centralizer to its actual
fixed points in the degree-3510 permutation representation. The generator lies
in the kernel of this action. The image is a concrete group, with no unitary
identification built into its definition.

This is the action used to construct the central quotient in GLS3, Table 5.3t
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`). The involution order, kernel bound,
and comparison with the matrix group U₆(2) require separate proofs.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi22

open Theory.GroupAction

/-- The first ATLAS generator as an element of its generated group. -/
def atlasA : Carrier := ⟨generatorA, Subgroup.subset_closure (by simp)⟩

theorem inclusion_atlasA : inclusion atlasA = generatorA := rfl

/-- The centralizer inside the actual generated permutation group. -/
def centralizerA : Subgroup Carrier := Subgroup.centralizer {atlasA}

/-- Points fixed by the first generator. -/
abbrev FixedPointsA := CentralizerFixedPoints.Points inclusion atlasA

/-- The restriction of the centralizer to the actual fixed points. -/
def fixedPointAction : centralizerA →* Equiv.Perm FixedPointsA :=
  CentralizerFixedPoints.action inclusion atlasA

theorem fixedPointAction_apply (g : centralizerA) (i : FixedPointsA) :
    (fixedPointAction g i).val = inclusion g.val i.val :=
  CentralizerFixedPoints.action_apply inclusion atlasA g i

/-- The generator, viewed in its own centralizer. -/
def centralAtlasA : centralizerA := CentralizerFixedPoints.centralElement atlasA

theorem centralAtlasA_mem_ker : centralAtlasA ∈ fixedPointAction.ker :=
  CentralizerFixedPoints.centralElement_mem_ker inclusion atlasA

/-- The concrete permutation image, without a group-family identification. -/
abbrev FixedPointImage := fixedPointAction.range

def fixedPointProjection : centralizerA →* FixedPointImage := fixedPointAction.rangeRestrict

theorem fixedPointProjection_surjective : Function.Surjective fixedPointProjection :=
  fixedPointAction.rangeRestrict_surjective

theorem fixedPointProjection_ker : fixedPointProjection.ker = fixedPointAction.ker :=
  fixedPointAction.ker_rangeRestrict

end Sporadic.Fischer.Fi22
