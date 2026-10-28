module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.CommonFacts
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules

/-!
# The Section 3 inputs already supplied to the regular-path argument

CommonFacts contains the actual natural-module marking and splitting. The
proved critical-module theorems supply index reciprocity, the commutator order
and the radius-two class bound. This assembles ModuleFacts without invoking
the unfinished constructor from LocalSource. Constructing CommonFacts itself
remains the common-reduction owner's obligation.

Source: Meierfrankenfeld--Stellmacher (1993), binary cases of (3.5), (3.9),
and (4.1), printed pp.869--870, 879, 881--882.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Keep the same literal natural marking supplied by the common source facts. -/
def naturalStructure {source : LocalSource L R} (common : CommonFacts R source geometry) :
    BinaryNaturalStructure source where
  X_eq_Z := common.X_eq_Z
  natural := common.natural
  decomposition := common.decomposition
  disjoint := common.disjoint

/-- The critical-module theorems discharge all remaining Section 3 fields. -/
def moduleFacts [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) : ModuleFacts source geometry where
  X_eq_Z := common.X_eq_Z
  natural := common.natural
  full_commutation := common.full_commutation
  decomposition := common.decomposition
  disjoint := common.disjoint
  critical_U_index := (naturalStructure common).critical_U_index geometry common.large_distance
  critical_Z_commutator_card :=
    (naturalStructure common).critical_Z_commutator_card geometry common.large_distance
  b_four_class_two := (naturalStructure common).b_four_class_two geometry


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
