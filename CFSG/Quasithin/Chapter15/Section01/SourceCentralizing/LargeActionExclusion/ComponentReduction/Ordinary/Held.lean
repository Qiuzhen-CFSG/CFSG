module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction
public import Theory.SpecificGroups.Held.ComponentFacts

/-!
# Excluding the ordinary Held component on exchanged source data

The intrinsic Held three-rank, outer-two and Sylow-fixer results supply every
model premise of the ordinary centralizer comparison. The comparison concerns
the original quotient L/O₂(L), so central two-covers are retained. The fixed
plane then contradicts that equality for either exchanged source row.

Source: Aschbacher--Smith 15.1.22(5), 15.1.25(1),(3), and 15.1.26,
printed pp.1100,1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The source ordinary Held row is impossible for both plane sizes. -/
theorem ExchangedSource.not_ordinary_held {d : CaseIComponentData T M Mc V}
    (s : d.ExchangedSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Held.He) := by
  rintro ⟨e⟩
  let := s.quasisimple
  have hf : Facts (d.L ⧸ pCore 2 d.L) := Facts.of_equiv e
    ⟨Held.LocalPairs.center_eq_bot, Held.three_rank_ge_two, Held.outer_isPGroup_two⟩
  exact s.no_equal_centralizers hG hM.1.2 h hf
    (d.ordinary_source_centralizer_of_model hG hM.1.2 hu h hL s.odd_core
      s.component_sylow hf e
      (fun P A hA hfix => @Held.elementary_sylow_fixer_card_le_two P A hA hfix)
      s.cubic_escape)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
