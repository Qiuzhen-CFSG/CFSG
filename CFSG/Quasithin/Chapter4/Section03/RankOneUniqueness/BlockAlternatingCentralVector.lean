module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternating
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.Centrality

/-!
# Applying the A₇ central-vector theorem to rank-one uniqueness

The proved specialized C.6.4(10) supplies the centrality premise in the
ordinary A₇ branch of original 4.3.7, printed p.616. The only remaining
branch-specific input is the explicit BlockAlternatingMarking on the
actual configuration. Its construction and final branch assembly belong
to the independent marking and rank-one block-alternating owners.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual 4.3.7 consumer, with its C.6.4 centrality premise discharged. -/
theorem SourceConfiguration.false_of_alternating_marking_centralVector
    (c : SourceConfiguration T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : BlockAlternatingMarking c) : False :=
  c.false_of_alternating_marking D h d
    (fun input => input.commutator_centralizes)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
