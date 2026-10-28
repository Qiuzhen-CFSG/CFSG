module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockReductionLinearThree
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockReductionRankTwo
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerComplete

/-!
# The complete reducible Sylow-normalizer implication

The four literal reducible models now all exclude an escaping normalizer.
This discharges the retained block-reduction source and connects it to the
independent block-centralizer theorem. The only earlier input to that
universal source contract is the guarded seven-row module classification.
A separate rowwise version consumes the alternatives on the original choice.

Source: Aschbacher–Smith 3.3.1 and 12.2.16, pp.586,799–800.
The genuine classification remains with qt-d-1222-modules and final Chapter12
assembly; no block, residual, geometry, or normalizer callback remains here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Complete source block reduction, conditional only on the earlier module theorem. -/
theorem blockReductionSource
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple) :
    BlockReductionSource T L V :=
  blockReductionSource_of_model_constructions modules linearThreeBlockConstruction
    alternatingSixBlockConstruction g2BlockConstruction alternatingEightResidualConstruction

/-- The original Sylow-normalizer source contract with both block inputs discharged. -/
theorem sylow_normalizer_le_of_modules
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_block_sources h D structural hnone hne
    (blockReductionSource modules) blockCentralizerSource

/-- Rowwise normalizer control on the unchanged original chosen module. -/
theorem sylow_normalizer_le_of_module_alternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) (rows : ModuleAlternatives1222 D) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  cases reducibleModels_of_module_alternatives h D hne rows with
  | linearThree E => exact sylow_normalizer_le_of_slThree_extension h D structural hnone hne E
  | alternatingSix E => exact sylow_normalizer_le_of_alternatingSix_core h D structural hnone hne E
  | g2 E => exact sylow_normalizer_le_of_g2_weyl_model h D structural hnone hne E
  | alternatingEight E => exact sylow_normalizer_le_of_alternatingEight_core h D structural hne E

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
