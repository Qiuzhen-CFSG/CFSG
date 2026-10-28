module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerNonalternatingComplete
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternatingComplete
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerLocalG2

/-!
# The complete surviving-block centralizer source

The A₆ terminal branch supplies its actual invariant-core geometry. The G₂(2)
and L₃(2) branches use the intrinsic natural-module bounds to put Ω₁Z(T) in
the original chosen module, where fixed-line weak closure proves the required
normalizer containment. All three branches contradict an escaping normalizer.

This module assembles the exact BlockCentralizerSource contract. It also
constructs the remaining L₃ local invariance on the literal residual, core,
and commutator preimage. The final normalizer consumer retains only the
independent block-reduction input, owned by qt-d-12216-sylow-normalizer.
No local geometry, action identification, or movement premise remains.

Source: Aschbacher–Smith 3.3.23–31, pp.598–602; 12.2.16, pp.799–800.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- Simultaneous normalization of L and T preserves each literal local construction. -/
theorem blockLocalInvariance_of_component_normalizer
    (hn : normalizer (T : Set G) ≤ normalizer (L : Set G)) : BlockLocalInvariance T L := by
  let N := normalizer (T : Set G)
  have hE := normalizer_le_normalizer_omegaCenterIn (T : Subgroup G)
  have hC := hE.trans (normalizer_le_normalizer_centralizer (omegaCenterIn (T : Subgroup G)))
  have hLC : N ≤ normalizer (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Set G) :=
    (le_inf hn hC).trans inf_normalizer_le_normalizer_inf
  have hX : N ≤ normalizer (blockLocalResidual T L : Set G) :=
    hLC.trans (normalizer_le_normalizer_characteristic_image
      (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G)) (pResidual 2 _))
  have hXT : N ≤ normalizer (blockLocalResidual T L ⊔ (T : Subgroup G) : Subgroup G) :=
    (le_inf hX le_rfl).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hR : N ≤ normalizer (blockLocalCore T L : Set G) :=
    hXT.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hH : N ≤ normalizer (L ⊔ (T : Subgroup G) : Subgroup G) :=
    (le_inf hn le_rfl).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQ : N ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    hH.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  refine ⟨fun _ => ⟨hX,hR⟩, fun _ => ?_⟩
  exact commutatorPreimage_normalized _ _ _ N
    ((T : Subgroup G).le_normalizer.trans hQ) le_rfl le_rfl hQ

/-- The literal local residual, local core, and central preimage are invariant
in the L₃(2) row, using only the original reducible consumer hypotheses. -/
theorem blockLocalInvariance_of_linearThree
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsLinearTwoBlock L 3) :
    BlockLocalInvariance T L :=
  blockLocalInvariance_of_component_normalizer
    (sylow_normalizer_le_of_linearThree_block h D structural hnone hfixed hb)

/-- All local invariance inputs at the actual surviving-block consumer. -/
theorem blockLocalInvarianceSource : BlockLocalInvarianceSource T L V := by
  intro h D structural hnone hfixed _ hb
  rcases hb with hb | hb | hb
  · exact blockLocalInvariance_of_alternating h D hfixed hb
  · exact blockLocalInvariance_of_g2Two h D hfixed hb
  · exact blockLocalInvariance_of_linearThree h D structural hnone hfixed hb

/-- The complete terminal surviving-block source implication, with no extra
geometry, movement, model, or normalizer assumptions. -/
theorem blockCentralizerSource : BlockCentralizerSource T L V :=
  blockCentralizerSource_of_local_branches blockLocalInvarianceSource
    nonalternatingBlockCentralizerSource alternatingBlockCentralizerSource

/-- Direct application of all three terminal branches to the intrinsic block alternative. -/
theorem sylow_normalizer_le_of_block_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : BlockAlternative L) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  exact sylow_centralizer_ne_bot D hfixed
    (blockCentralizerSource h D structural hnone hfixed hescape hb)

/-- Actual application to the original normalizer consumer. The independent
block-reduction source remains with qt-d-12216-sylow-normalizer; all terminal
centralizer and local invariance premises are discharged here. -/
theorem sylow_normalizer_le_of_block_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (reduction : BlockReductionSource T L V) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_block_sources h D structural hnone hfixed reduction blockCentralizerSource

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
