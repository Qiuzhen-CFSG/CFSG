module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Source
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
/-!
# Exact C.1.9 for the Chapter E overgroups

Apply the complete block commutation theorem inside each original overgroup.
The upper two-three core guard agrees definitionally with `C19Condition`;
all short-group, subnormality, and conjugation data remain unchanged.

Source: Aschbacher–Smith, C.1.9 and E.6.23.
-/
public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
open Subgroup
/-- The exact C.1.9 input, now supplied for all actual ambient overgroups. -/
theorem source_blockCommutationInput (G : Type*) [Group G] [Finite G] :
    BlockCommutationInput G := by
  intro H hH B D hB hD hne
  exact ChapterC.blocks_commute hH hB hD hne
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
