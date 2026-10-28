module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.KnownSimple.FFSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.Source

/-!
# Constructing the single characteristic pair in the original Theorem E source

The central omega subgroup makes the actual Baumann subgroup nontrivial.
Its original Sylow containment and proved Baumann idempotence give precisely
the hypotheses of full C.1.18. One characteristic pair is then chosen before
all local embeddings and supplied to the small-center and many-overgroup
source arguments. Neither the pair nor its universal property is an input.

The small-center conclusion retains only the genuine earlier3.1.1 source
implication. The large-center route keeps its independent remaining source
classifications and residual theorem explicitly.
Source: Aschbacher--Smith C.1.18--19 and15.4.7--25.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
open ChapterC.GlaubermanNiles
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
open LocalSetup.SourceWitnesses LocalSetup.EmbeddingReduction
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u v
variable {G : Type u} [Group G] [Finite G]

theorem source_baumann_universal_pair (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) :
    ∃ D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)), D.Universal.{u,v} := by
  let B := ChapterB.baumann (T : Subgroup G)
  have hZB : omegaOneCenterAmbient (T : Subgroup G) ≤ B := by
    intro z hz
    obtain ⟨hzt,_,hzc⟩ := (mem_omegaOneCenterAmbient_iff _ z).mp hz
    refine ⟨hzt,?_⟩
    intro a ha
    exact hzc a ((show elementaryAbelianMaxJ (T : Subgroup G) ≤ T from
      sSup_le fun _ hA => hA.1) ((mem_omegaOneCenterAmbient_iff _ _).mp ha).1)
  have hBne : B ≠ ⊥ := fun hb => centralOmega_ne_bot hG T (bot_unique (hb ▸ hZB))
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hBne
  exact exists_universal_characteristicPair (T.isPGroup'.to_le inf_le_left)
    (SmallCenter.baumann_isBaumannFixed T)
theorem source_small_center_theoremE_from_uniform_sources
    (h311 : RatioSource.Earlier311 (G := G))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    : ClassificationModels.IsTheoremEModel G := by
  obtain ⟨D,hD⟩ := source_baumann_universal_pair.{u,u} hG T
  exact source_small_center_theoremE_from_source1391 h311 hG T hempty hmany hZ D hD

theorem source_many_theoremE_from_uniform_sources
    (h311 : RatioSource.Earlier311 (G := G))
    (classification : SingleOvergroup.GoldschmidtClassification.{u})
    (orbits : ComponentOrbitTheorem.{u} KnownSimple.IsKnownSimple)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (c27 : LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.UniversalC27.{u})
    (c134 : LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (sourceF : FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    : ClassificationModels.IsTheoremEModel G := by
  obtain ⟨D,hD⟩ := source_baumann_universal_pair.{u,u} hG T
  exact source_many_theoremE_from_classifiedFF h311 classification orbits residual c27 c134 sourceF hG T hempty hmany D hD

end CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
