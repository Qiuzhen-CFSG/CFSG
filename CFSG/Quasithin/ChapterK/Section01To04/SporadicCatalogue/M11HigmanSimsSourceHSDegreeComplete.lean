module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceHSDegree
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact

/-!
# The HS binary degree window on the original source action

Faithfulness of the literal thirteen-relator ATLAS presentation discharges the
remaining descent input for the degree-896 pair and degree-1408 model. Together
with the other constructed simple models, these saturate the bound of nine
odd-order conjugacy classes and prove completeness in degrees at most fifty.
The universal comparison with the binary twenty-space then supplies the trace
calculation that descends the commuting field to F₂, excluding binary degree
forty. The two-group center bound removes the source cover's center, so the
conclusion concerns the original vector space and ambient representation.

The degree window below has no extra hypotheses. Its source-exclusion and
rank-one applications retain only the independent outer estimates in degree
twenty; the final unconditional HS exclusion remains with their assembly owner.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, published pp.366--367 (author-preprint pp.16--17), and
Theorem 6.6/Table 6.7; Aschbacher--Smith K.4, printed p.457/PDF p.468.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Subgroup
universe u v

/-- Every original faithful binary HS source action in dimension at most fifty
has dimension twenty. Completeness, presentation faithfulness and binary field
descent are all discharged, without a cubic or FF hypothesis. -/
theorem higmanSimsDegreeWindow : HigmanSimsDegreeWindow.{u,v} :=
  higmanSimsDegreeWindow_of_presentationFaithful
    _root_.Sporadic.LeechRelated.HS.AtlasPresentation.toCarrier_injective

/-- Discharge the degree premise in the literal Chapter K source exclusion.
Only the independently owned outer estimates remain explicit. -/
theorem sourceExclusion_hs_of_outer
    (houter : HigmanSimsOuterEstimates.{u,v}) : SourceExclusion.{u,v} .hs :=
  sourceExclusion_hs_of_degree_and_outer higmanSimsDegreeWindow houter

/-- Apply the completed degree window through the original rank-one source
identification of the generalized Fitting subgroup and its central quotient. -/
theorem not_hs_of_rankOne_source_of_outer
    (houter : HigmanSimsOuterEstimates.{u,v})
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.hs.Carrier)) : False :=
  not_hs_of_rankOne_source_of_degree_and_outer higmanSimsDegreeWindow houter h he

end CFSG.Quasithin.ChapterK.SporadicCatalogue
