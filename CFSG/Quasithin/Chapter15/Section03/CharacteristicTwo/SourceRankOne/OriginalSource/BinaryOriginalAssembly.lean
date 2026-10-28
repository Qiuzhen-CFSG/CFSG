module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.ReplacementAssembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.OriginalEarlier

/-!
# Original binary exclusion from the first-plane displacement

The original first plane has nontrivial central displacement of order two on
the component's commutator core. The large-distance core theorem excludes
this displacement, using the actual earlier MS inputs now constructed on the
original setup. Abelian and distance-four cores were already excluded.

This argument retains the original component, Sylow subgroup, first plane and
full quotient marking. It never transfers centrality of the replacement's
fixed four-group to the original two-core, and uses no whole-fixed-factor
equality. Thus the original 15.3.25 consumer needs only the independent
nonbinary core branches (or C.1.32), rather than the full C.1.34 implication.

Source: Aschbacher--Smith 15.3.25--32, printed pp.1130--1134;
Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.5) and section 7.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.MarkedMS
open SmallExtension.CentralCover
open ChapterC BinaryMS.MS93 BinaryMS.MS93.DistanceEight.PathCentrality
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original large binary setup is impossible after all earlier MS
inputs have been supplied by their proved original-source construction. -/
theorem source_binary_large_false_of_original_source
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL)
    (t : InputSetup (source_binaryMSInput s e))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical) : False :=
  source_binary_large_false s hm e t common
    (Source44.OriginalEarlier.earlier common hb)

/-- The literal binary parabolic row is excluded without a full MS
classification or an action premise on the original fixed factor. -/
theorem source_linearThree_false
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L LinearThree.SL Parabolics.linearThreeParabolic) :
    False := by
  apply source_linearThree_false_of_large_distance s m
  intro e t hc hb
  obtain ⟨common⟩ := t.commonFacts hc
  exact source_binary_large_false_of_original_source s (.linearThree m) e t common hb

/-- The full intrinsic binary quotient selects the literal binary parabolic
and excludes the original small component. Central covers are retained. -/
theorem source_binary_false_of_coreQuotient
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL) : False := by
  obtain ⟨m⟩ := source_binary_parabolic_of_coreQuotient s hm e
  exact source_linearThree_false s m

/-- The original selection hypotheses exclude their actual binary small
component, with no extra fixed-factor or original-core centrality premise. -/
theorem source_binary_false_of_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL) : False := by
  obtain ⟨s⟩ := source_smallData hG d hempty hM hu hmany hshadow hI hf c
  exact source_binary_false_of_coreQuotient s hm e

/-- Original 15.3.25 retains only the independently owned alternating-six
and binary G₂ whole-core branches. Its binary branch is proved here. -/
theorem source_lemma_15_3_25_of_nonbinary_core_branches
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (hA6 : ∀ {I : Subgroup G} (c : ComponentWitness d I),
      SourceData KnownSimple.IsKnownSimple d c →
      Parabolics.RankTwoParabolicMarking d I c.L
        (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) Parabolics.symplecticDerivedParabolic →
      IsBlock (c.L.subgroupOf (c.L ⊔ d.S)) ∧ IsAlternatingBlock c.L 6)
    (hG2 : ∀ {I : Subgroup G} (c : ComponentWitness d I),
      SourceData KnownSimple.IsKnownSimple d c →
      Parabolics.RankTwoParabolicMarking d I c.L
        (commutator (Atlas.G2.Model (ZMod 2))) Parabolics.g2DerivedParabolic →
      IsBlock (c.L.subgroupOf (c.L ⊔ d.S)) ∧
        Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsG2TwoBlock c.L) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  apply source_lemma_15_3_25_of_small_core_branches hG d hempty hM hu hmany hshadow hA6 hG2
  intro I c s m e t hc hb
  obtain ⟨common⟩ := t.commonFacts hc
  exact source_binary_large_false_of_original_source s (.linearThree m) e t common hb

/-- The original rank-one consumer of C.1.32 needs no additional binary MS
classification: the original first-plane argument supplies that branch. -/
theorem source_lemma_15_3_25_of_rankTwo_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (rankTwo : ∀ {I : Subgroup G} (c : ComponentWitness d I),
      SourceData KnownSimple.IsKnownSimple d c →
      Parabolics.SmallParabolicMarking d I c.L → RankTwoAlternatives c.L d.S) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  apply source_lemma_15_3_25_of_rankTwo_and_replacement hG d hempty hM hu hmany hshadow rankTwo
  intro I c s e t common hb a a' p hp
  exact Source44.Replacement.OriginalSource.prescribedReplacement common hb p hp

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
