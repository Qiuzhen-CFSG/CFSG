module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.NaturalEight
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.LocalFamily
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Containment.KnownSimple

/-!
# The actual containing component in the fixed-line centralizer

The natural-eight branch supplies its fixed line of order two. Original
15.3.11 makes the common subgroup S Sylow in its centralizer, and the
full-catalogue A.3.12 containment theorem supplies a unique C-component
containing the original L. The proper-embedding exclusions are separate;
this result assumes neither that the containing component is L nor the
residual-centralizer conclusion.

Source: Aschbacher–Smith15.3.32(3), printed p.1133, using1.2.4 andA.3.12.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration EightGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The containing component in the original fixed-line centralizer, with
all earlier containment and local-family premises discharged. -/
theorem source_fixedLine_containing_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (mark : Parabolics.MiddleNodeFlagMarking d I c.L) :
    ∃! K : Subgroup G, K ∈ Chapter1.cComponentsIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)) ∧ c.L ≤ K := by
  obtain ⟨a⟩ := source_lieSieve_input hG d hempty hM hu hmany hshadow hI hf c
  obtain ⟨_,_,_,_,hfixed,hcard,_⟩ :=
    source_lemma_15_3_32_1_2 hG d hempty hM hu hmany hshadow hI hf c mark
  apply existsUnique_component_over_fixedLine hG
    (fun _ _ _ => ChapterA.Section03.SourceComponents.containment_knownSimple)
    d hI.1 c a.normal a.generated hfixed hcard
  intro J hJ
  exact (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany J hJ).sylow

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
