module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Parabolics
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.SmallModuleSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.NaturalCoreModels.SourceWitnesses.AllModels

/-!
# The original small-branch consumer of the MS core classification

Original15.3.26–29 constructs the exact small MS-pair, and corrected B.5
constructs its actual marked V₂ constituent. The only remaining input is
the small core classification at this literal pair. Its surviving A₆,G₂,
and three binary linear core models feed the existing complete exclusions.

Source: Aschbacher–Smith15.3.31, printed p.1132.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension
open EightGeometry.NaturalModule.Recognition
variable {G : Type*} [Group G] [Finite G]

/-- Every local source datum for the small-component argument follows from
the original selection hypotheses. -/
theorem source_smallData
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) : Nonempty (SourceData KnownSimple.IsKnownSimple d c) := by
  obtain ⟨a⟩ := source_lieSieve_input hG d hempty hM hu hmany hshadow hI hf c
  exact ⟨{
    minimal := hI
    sqtk := OutsideStructure.outside_sqtk hG d hI.1
    characteristicTwo := hf
    rank := a.rank
    facts := a.facts
    solvableControl := a.solvableControl
    normal := a.normal
    contains := a.contains
    sylow := a.sylow
    sylow_eq := a.sylow_eq
    characteristic := (source_lemma_15_3_29 hG d hempty hM hu hmany hshadow hI.1).1
    line := source_lineData hG d hempty hM hu hmany hshadow hI.1
    yRank := source_y_three_rank hG d hempty hM hu hmany
    omega := source_central_omega d }⟩

/-- The exact small MS-pair at the original component and Sylow subgroup. -/
theorem source_smallMSPair
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    MarkedMS.SmallMSPair KnownSimple.IsKnownSimple c.L d.S :=
  MarkedMS.smallMSPair_of_source d c s.sqtk s.characteristicTwo s.generated s.normal
    ⟨s.sylow,s.sylow_eq⟩ s.characteristic hm

/-- The source31 consumer, with only the actual C.1.32/C.1.34 core output
remaining explicit. All FF and V₂ marking inputs are discharged here. -/
theorem source_small_false_of_MS_cases
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (hcases : MarkedMS.SurvivingSmallCases c.L d.S)
    (hsimple : IsSimpleGroup (c.L ⧸ pCore 2 c.L)) : False := by
  let _ := hsimple
  let _ := component_internal_elementary d c s.characteristicTwo s.sylow s.sylow_eq
  have hVT := d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le)
  obtain ⟨hw,hd⟩ := MarkedMS.Constituents.marked_alternative_of_adequate_source d c
    s.normal s.generated s.characteristicTwo s.sylow s.sylow_eq s.line s.contains
    s.rank s.yRank hVT s.sqtk hm
  have ms : MarkedMS.SmallMSConclusion KnownSimple.IsKnownSimple d c s.normal s.generated
      s.characteristicTwo s.sylow s.sylow_eq := by
    refine ⟨source_smallMSPair s hm,hcases,hsimple,?_,?_,hw,?_⟩
    · exact ⟨coreQuotientEquivStar d c s.normal s.sylow s.sylow_eq,
        coreQuotientEquivStar_apply d c s.normal s.sylow s.sylow_eq⟩
    · exact (extensionCore_eq_overgroup d c s.contains s.normal).trans
        (congrArg (fun J : Subgroup G => ⁅J.pCoreIn 2,c.L⁆) s.generated)
    · rcases hd with h | ⟨e,⟨b⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨e,b,MarkedMS.Constituents.binaryLine_copy_markings _ e _ _ b⟩
  exact NaturalCoreModels.SourceWitnesses.excluded_of_source s hm ms

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
