module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.A6Intrinsic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.G2Holomorph
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ShortCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility

/-!
# The original alternating-six branch from core reconstruction

The original component source supplies the group-theoretic clauses of shortness,
and the natural module supplies irreducibility. Thus the remaining structural
input is precisely that the whole commutator core is elementary and centralized
by O₂(L). Exhaustion by the actual Sylow-central component module is one sufficient
way to establish those two assertions. The original parabolic map is retained
through the natural-core contradiction.

These core assertions and the natural model remain genuine MS93 inputs; this
module does not infer them from the existence of a natural constituent.
Source: Aschbacher–Smith C.1.7, C.1.32 and 15.3.31, pp.123,135–136,1132.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
open CentralCover.BlockModels
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- Source group structure and the natural model discharge all other shortness clauses. -/
theorem source_alternating_short_of_core
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (he : IsElementaryAbelian 2 (ChapterC.blockU c.L))
    (hc : ChapterC.blockU c.L ≤ centralizer (pCore 2 c.L : Set c.L))
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction Alternating.action)) :
    ChapterC.IsShort c.L := by
  have hm : ChapterC.IsLinearBlockModel c.L Alternating.action :=
    ⟨multiplicativeAction Alternating.action, ⟨model⟩, fun _ _ => rfl⟩
  exact s.short_of_core he hc hm.alternating_six_irreducible

/-- The exact elementary and central whole-core output suffices at the original pair. -/
theorem source_alternating_false_of_elementary_central_core
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
      Parabolics.symplecticDerivedParabolic)
    (he : IsElementaryAbelian 2 (ChapterC.blockU c.L))
    (hc : ChapterC.blockU c.L ≤ centralizer (pCore 2 c.L : Set c.L))
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction Alternating.action)) : False :=
  source_alternating_false_of_natural_core s m
    (source_alternating_short_of_core s he hc model) model

/-- Actual component-module exhaustion gives the required whole-core structure. -/
theorem source_alternating_false_of_core_reconstruction
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
      Parabolics.symplecticDerivedParabolic)
    (hQ : extensionCore c.L = d.componentModule I c.L)
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction Alternating.action)) : False :=
  source_alternating_false_of_elementary_central_core s m
    (s.core_elementary_of_eq_componentModule hQ)
    (s.core_central_of_eq_componentModule hQ) model

/-- Literal original 15.3.31 consumer of the remaining core-reconstruction input. -/
theorem source_lemma_15_3_31_alternating_core_reconstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
      Parabolics.symplecticDerivedParabolic)
    (hQ : extensionCore c.L = d.componentModule I c.L)
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction Alternating.action)) : False := by
  obtain ⟨s⟩ := source_smallData hG d hempty hM hu hmany hshadow hI hf c
  exact source_alternating_false_of_core_reconstruction s m hQ model

/-- The actual free-holomorph core bound supplies the two structural clauses.
The source-native MS93 core is retained, without identifying it with the
separately constructed FF component module. -/
theorem source_alternating_false_of_holomorph_core_le_X
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
      Parabolics.symplecticDerivedParabolic)
    (hX : ChapterC.BinaryMS.MS93.core (d.S.subgroupOf I)
        (ChapterC.BinaryMS.MS93.alpha (d.S.subgroupOf I)) ≤
      ChapterC.BinaryMS.MS93.X (d.S.subgroupOf I)
        (ChapterC.BinaryMS.MS93.alpha (d.S.subgroupOf I)))
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction Alternating.action)) : False :=
  source_alternating_false_of_elementary_central_core s m
    (G2Holomorph.blockCore_elementary s hX) (G2Holomorph.blockCore_central s hX) model

/-- Literal application of MS93's core identity at the original component. -/
theorem source_alternating_false_of_holomorph_core_eq_U
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
      Parabolics.symplecticDerivedParabolic)
    (hU : ChapterC.BinaryMS.MS93.core (d.S.subgroupOf I)
        (ChapterC.BinaryMS.MS93.alpha (d.S.subgroupOf I)) =
      ChapterC.BinaryMS.MS93.U (d.S.subgroupOf I)
        (ChapterC.BinaryMS.MS93.alpha (d.S.subgroupOf I)))
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction Alternating.action)) : False :=
  source_alternating_false_of_holomorph_core_le_X s m
    (G2Holomorph.core_le_X_of_eq_U s hU) model

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
