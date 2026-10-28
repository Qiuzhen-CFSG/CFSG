module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceSevenEscape
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceInheritance
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.SourceReduction
/-!
# The exact E.6.18 consumer with escape and normality supplied by source

The direct seven-model action calculation supplies the escaping hyperplane.
The genuine common-normal theorem supplies E.6.13. The corrected original
corank-two lifting argument then proves SevenExcluded, invoking its model
lifting only after the source argument has established m > 2.

The remaining premise is precisely that source lifting, owned by its complete
model inspection. No unrestricted SevenActionInspection is assumed.
Source: Aschbacher–Smith, E.6.8(4),E.6.13,E.6.18, pp.248,250,252.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes
open ComponentBalance Enlargement
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

theorem source_sevenExcluded_of_corank_two_lifting [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (hlift : 2 < localM V → SevenCorankTwoLifting V) : SevenExcluded M V :=
  sevenExcluded_of_corank_two_lifting h h15
    (Components.RemainingSieve.source_sevenEscape h)
    (source_obstruction_not_sylow_normalized h h311) hlift
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes
