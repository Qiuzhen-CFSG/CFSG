module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Parabolics
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.FFClassification
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.DegreeEight
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.MiddleNaturalMarking
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SpanSplittingSource

/-!
# The original degree-eight natural action and fixed planes

Apply the corrected FF table to the actual marked component. The proved
cover-kernel theorem identifies I/O₂(I) with the original star quotient,
so the actual local SQTK hypothesis supplies the component SQTK input.
The original orthogonal geometry gives every plane and seed-span premise.
Thus the natural action and both core-centralizer identities follow with
no remaining B.4/B.5, multiplier, cohomology or B.2.14 source hypothesis.

Source: Aschbacher–Smith15.3.32(1),(2), printed pp.1132–1133.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration
open EightGeometry.NaturalModule
variable {G : Type*} [Group G] [Finite G]

/-- The actual middle-node branch has the natural six-dimensional action
and the source fixed-line and fixed-plane identities. -/
theorem source_lemma_15_3_32_1_2
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (mark : Parabolics.MiddleNodeFlagMarking d I c.L) :
    ∃ a : NaturalEightAction I (d.componentModule I c.L),
      a.actor = mark.equiv.toMonoidHom.comp (d.starMap I) ∧
      I.pCoreIn 2 = I ⊓ centralizer (d.componentModule I c.L : Set G) ∧
      I.pCoreIn 2 = d.S ⊓ centralizer (d.componentModule I c.L : Set G) ∧
      d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁ ∧
      Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2 ∧
      d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂ := by
  obtain ⟨input⟩ := source_lieSieve_input hG d hempty hM hu hmany hshadow hI hf c
  have hline := source_lineData hG d hempty hM hu hmany hshadow hI.1
  have hOmega := source_central_omega d
  have hlocal := OutsideStructure.outside_sqtk hG d hI.1
  have hstar : IsSQTK KnownSimple.IsKnownSimple (d.Star I) :=
    (IsSQTK.equiv (coreEquivStar d c input.normal input.generated input.sylow input.sylow_eq
      mark.equiv mark.component SourceInputs.eightCoverKernelTwo)).mp
      (StarSelection.Lifting.sqtk_twoCore_quotient hlocal)
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have h7 := source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have hspan := source_residual_seed_span hG d.T hempty d.action hM hu hmany hne
  have hseed := OutsideStructure.LocalBranches.second_choice_plane_le_span d
    input.facts.choice h7.1 hspan
  obtain ⟨naturalMark⟩ := mark.naturalMarking
  exact SourceInputs.DegreeEight.natural_module_of_source d c input.normal input.generated
    input.sylow input.sylow_eq mark.equiv mark.component SourceInputs.FFClassification.classification
    FixedGeometry.sourceB214Splitting hf (hstar.subgroup _) input.contains input.rank
    (source_y_three_rank hG d hempty hM hu hmany) hline.theta_eq hline.normalizer_eq
    hline.plane_eq hline.plane_full hseed
    (d.action.planeStabilizer_index_two d.T d.sylow_le 1)
    (d.action.card_centralInvolutions d.T d.sylow_le) hOmega.2 hOmega.1 naturalMark

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
