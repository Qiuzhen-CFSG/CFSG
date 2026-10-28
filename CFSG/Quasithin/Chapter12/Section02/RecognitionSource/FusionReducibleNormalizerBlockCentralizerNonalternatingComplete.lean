module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerChosenModel
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerChosenCover
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerContracts
public import Theory.Representation.G2BinaryFixedBounds
public import Theory.Representation.PSL3Two.NaturalDualCohomology
public import Theory.Representation.PSL3Two.NaturalSylowFixed

/-!
# Completion of the nonalternating surviving-block branches

For both G₂(2)′ on its natural six-space and SL₃(2) on its natural three-space,
the dual first cohomology has dimension one and a Sylow 2-subgroup fixes at
most a line. The intrinsic block model identifies the actual chosen central
quotient with that natural action. Hence |C_V(L)|=2 and |C_V(T)|≤4.

The fixed-line argument then proves N_G(T)≤N_G(L) using the original NoEscape
hypothesis. This closes both terminal centralizer branches at the precise
12.2.16 consumer, without additional movement, model, or invariance premises.
The earlier invariant-core proofs for A₆ are assembled separately.

Source: Aschbacher–Smith 3.3.25–31, pp.599–602; 12.2.16, pp.799–800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Apply natural-module fixed bounds to the original chosen module and normalizer. -/
theorem sylow_normalizer_le_of_block_model_fixed_bounds
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsShort L)
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : A →* MulAut (Multiplicative W)} {σ : Representation (ZMod 2) A W}
    (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd = σ g v.toAdd)
    (hH : Module.finrank (ZMod 2) (H1 σ.dual) ≤ 1)
    (hS : ∀ P : Sylow 2 A, Nat.card (fixedSpace σ (P : Subgroup A)) ≤ 2) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let e := chosenCentralEquiv_of_blockModel D hb m hρ
  have hC := ChosenCover.fixed_card_eq_two D e hfixed hH
  exact sylow_normalizer_le_of_small_fixed_spaces h D structural hnone hb hC
    (ChosenCover.sylow_fixed_card_le_four D e hC hS)

/-- The G₂(2) block branch with every local premise discharged. -/
theorem sylow_normalizer_le_of_g2Two_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsG2TwoBlock L) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨m⟩ := hb.natural_model
  exact sylow_normalizer_le_of_block_model_fixed_bounds h D structural hnone hfixed hb.short
    m (σ := g2DerivedNatural (ZMod 2)) (fun _ _ => rfl)
    Atlas.G2.Natural.BinarySylowFixedSpace.derived_natural_dual_H1_finrank.le
    Atlas.G2.Natural.BinarySylowFixedSpace.card_derived_sylow_fixed_le_two

/-- The L₃(2) block branch with every local premise discharged. -/
theorem sylow_normalizer_le_of_linearThree_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsLinearTwoBlock L 3) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨ρ,⟨m⟩,hρ⟩ := hb.2.2.2
  exact sylow_normalizer_le_of_block_model_fixed_bounds h D structural hnone hfixed hb.2.1
    m hρ BinaryLinearThree.natural_dual_H1_finrank.le
    BinaryLinearThree.card_sylow_natural_fixed_le_two

/-- The exact retained nonalternating centralizer contract. -/
theorem nonalternatingBlockCentralizerSource : NonalternatingBlockCentralizerSource T L V := by
  intro h D structural hnone hfixed hescape _ hb
  rcases hb with hb | hb
  · exact (hescape (sylow_normalizer_le_of_g2Two_block h D structural hnone hfixed hb)).elim
  · exact (hescape (sylow_normalizer_le_of_linearThree_block h D structural hnone hfixed hb)).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
