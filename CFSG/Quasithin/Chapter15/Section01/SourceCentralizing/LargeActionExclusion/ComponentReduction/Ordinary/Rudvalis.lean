module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction
public import Theory.SpecificGroups.Rudvalis.ComponentFacts

/-!
# Excluding the ordinary Rudvalis component on exchanged source data

Simplicity of the actual central quotient transfers to the Rudvalis carrier;
no independent model simplicity theorem is needed. The intrinsic cubic and
Sylow-fixer facts then give equality of the two literal centralizers, which
contradicts exchanged fixed-plane movement. Central covers are retained.

This is a specialized alternative to the characteristic-subgroup argument
excluding Ru in source 15.1.22: it uses the later cubic escape and exchanged
planes already available to 15.1.26, and does not claim the earlier exclusion.
Source: Aschbacher--Smith 15.1.22(**), 15.1.25(1),(3), 15.1.26,
printed pp.1099--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The ordinary Rudvalis row is impossible with the actual exchanged planes. -/
theorem ExchangedSource.not_ordinary_rudvalis {d : CaseIComponentData T M Mc V}
    (s : d.ExchangedSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model) := by
  rintro ⟨e⟩
  let := s.quasisimple
  let := hL.2
  let a : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv a
  let : IsSimpleGroup (d.L ⧸ center d.L) := IsQuasisimple.simple
  let c : (d.L ⧸ center d.L) ≃* Rudvalis.Model :=
    (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  let : IsSimpleGroup Rudvalis.Model := c.symm.isSimpleGroup
  have hf : Facts (d.L ⧸ pCore 2 d.L) := Facts.of_equiv e
    ⟨Rudvalis.LowCentralizers.model_center_eq_bot, Rudvalis.three_rank_ge_two,
      Rudvalis.outer_isPGroup_two⟩
  exact s.no_equal_centralizers hG hM.1.2 h hf
    (d.ordinary_source_centralizer_of_model hG hM.1.2 hu h hL s.odd_core
      s.component_sylow hf e
      (fun P A hA hfix => @Rudvalis.elementary_sylow_fixer_card_le_two _ P A hA hfix)
      s.cubic_escape)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
