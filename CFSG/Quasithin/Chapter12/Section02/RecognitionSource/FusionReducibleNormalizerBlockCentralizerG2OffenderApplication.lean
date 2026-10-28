module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerG2CoreProduct
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.G2JoinOffenderGeneration
public import Theory.Representation.G2NaturalOffenders

/-!
# The literal G₂ offender application

The actual moved subgroup is used through its natural G₂ offender image.  The
actor bridge supplies the exact two-conjugate generation needed by the core
product theorem, while the centralizer-index bound remains an explicit source
input.  This avoids selecting a root-eight preimage, which would lose the
central kernel of the intrinsic block quotient.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- An actual binary-natural offender image and the sharp centralizer-index
bound force the literal local core to be elementary abelian. -/
theorem g2Two_core_elementary_of_offender_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsG2TwoBlock L)
    (m : ChapterC.BlockModuleModel L ChapterC.g2TwoNaturalAction)
    (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G))
    (hoff : IsOffender (Atlas.G2.NaturalOffenders.binaryNatural (F := ZMod 2))
      ((A.subgroupOf (L ⊔ (T : Subgroup G))).map
        (ChapterC.G2BlockAction.joinFullActor D.sylow_normalizes_component m)))
    (hi : (centralizer (A : Set G)).relIndex
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 8) :
    IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      frattini ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⊥ := by
  obtain ⟨g, hg, hgen⟩ := ChapterC.G2BlockAction.joinFullActor_generation_of_offender
    D.sylow_normalizes_component m A hA hoff
  exact g2Two_core_elementary_of_conjugate_index h D hfixed hescape hb A g hg hgen hi

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
