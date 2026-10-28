module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.FFPlacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Assembly

/-!
# Original rank-one marked parabolic alternatives

The original source hypotheses construct the normal component and its Y₊
containment. Minimality supplies the invariant-overgroup geometry. The
corrected adequate B.5 theorem gives the actual star component model,
which feeds the complete Lie sieve and simultaneous eight-point marking.

Source: Aschbacher–Smith15.3.27(4)–28, printed pp.1130–1131.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06
open RankOneConfiguration RankOneConfiguration.Parabolics
variable {G : Type*} [Group G] [Finite G]

/-- Every input to the marked parabolic sieve comes from the original local data. -/
theorem source_lieSieve_input
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) : Nonempty (LieSieve.Input d I c) := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI.1
  obtain ⟨P,hP⟩ := h11.sylow
  exact ⟨{
    minimal := hI
    characteristicTwo := hf
    rank := source_yplus_three_rank_one d h11 hshadow
    facts := source_lemma_15_3_26_1 hG d hempty hM hu hmany hshadow hI.1
    solvableControl := source_lemma_15_3_26_3 hG d hempty hM hu hmany hI.1 hf
    normal := source_lemma_15_3_27_1 hG d hempty hM hu hmany hshadow hI.1 hf c
    contains := source_lemma_15_3_27_2 hG d hempty hM hu hmany hshadow hI.1 hf c
    sylow := P
    sylow_eq := hP
    module_le := d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le)
    kernel_le := h11.centralizer_le }⟩

/-- Original15.3.27(4), including uniqueness among all proper overgroups. -/
theorem source_lemma_15_3_27_4
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) :
    I = c.L ⊔ d.S ∧ d.Yplus ⊔ d.S ≤ d.MI I ∧ d.MI I < I ∧
      ∀ J : Subgroup G, d.Yplus ⊔ d.S ≤ J → J < I → J ≤ d.MI I := by
  obtain ⟨a⟩ := source_lieSieve_input hG d hempty hM hu hmany hshadow hI hf c
  exact lemma_15_3_27_4_of_containment d hI c a.sylow a.sylow_eq a.contains
    (a.yplus_le_intersection.trans inf_le_left)

/-- Original15.3.28, with the complete corrected model list discharged. -/
theorem source_lemma_15_3_28
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) : MarkedAlternative d I c := by
  obtain ⟨a⟩ := source_lieSieve_input hG d hempty hM hu hmany hshadow hI hf c
  have hm := component_star_ff_model hG d hI.1 hf c ⟨a.sylow,a.sylow_eq⟩
  have hA7 := component_star_not_alternating_seven d c hI a.facts a.rank
    a.normal a.sylow a.sylow_eq
  cases LieSieve.lieParabolicAlternative a hm hA7 with
  | linearTwo F marking => exact .linearTwo F marking
  | small marking => exact .small marking
  | middle marking =>
    obtain ⟨flag⟩ := middleNodeFlagMarking_of_outerMiddleNodeData d c a.normal
      a.generated a.sylow a.sylow_eq a.kernel_le marking
    exact .middle flag

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
