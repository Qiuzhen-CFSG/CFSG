module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalMovingCubicPair
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SylowDisplacement
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeA5Residual
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreLeftAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.CubicDerivedBound

/-!
# The genuine original moving residual contradiction

The selected cubic source factor is the whole original residual because
that residual has its actual A₅ quotient. The original chosen module makes
the derived subgroup of the full cubic parabolic core have order at least
eight. The genuine mixed-pair source bound makes the same subgroup have
order at most four. Thus an original residual Context cannot occur for a
moving outside H of generation parameter greater than one.

All source selection and model comparisons are proved dependencies. No
5.2.3 classifier, ambient catalogue exclusion, or small-core bound is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric Chapter12.Section02
open CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H W W₁ W₂ W₃ : Subgroup G}

/-- The original moving H cannot carry the actual chosen residual module
once its genuine generation parameter exceeds one. -/
theorem original_moving_residual_context_impossible
    (d : Context T L V V₁ V₂ V₃)
    (e : Context T (residual H) W W₁ W₂ W₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      alternatingGroup (Fin 5)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) : False := by
  obtain ⟨A,B,R,c,hd,r,hr,hcore,hF11,⟨eU⟩⟩ :=
    original_moving_cubic_source_pair d e hmany hH hgen hm hZ
  have hR := hr.right_eq_residual_of_a5 r.right_le_residual hm.some
  subst R
  have h := Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient
  have hi := d.chosen.rankOne_generic_input_of_many h hmany (by decide : 1 < 2)
    (source523_setup_of_context d).linear
  let Q := ((A ⊔ Global.sourceS L H) ⊔ (B ⊓ residual H)).pCoreIn 2
  have hu : (T : Subgroup G) ⊓ L ≤ Q :=
    r.original_sylow_le_left_parabolic_core hi hH c hd
  have hv : V ≤ Q := (le_inf d.chosen.le_sylow d.chosen.le_component).trans hu
  have hlarge : 8 ≤ Nat.card (⁅Q,Q⁆ : Subgroup G) :=
    d.eight_le_card_sylow_commutator.trans (card_le_of_le (commutator_mono hv hu))
  have hp : ChapterF.Source.parabolic ![residual H,A ⊔ Global.sourceS L H]
      (Global.sourceS L H) 1 = (A ⊔ Global.sourceS L H) ⊔ (B ⊓ residual H) := by
    change (A ⊔ Global.sourceS L H) ⊔ Global.sourceS L H ⊔
      ChapterF.Source.borel (residual H) (Global.sourceS L H) = _
    rw [r.right_borel]
    rw [sup_assoc A (Global.sourceS L H) (Global.sourceS L H),sup_idem,←sup_assoc]
    rw [sup_eq_left.mpr (show Global.sourceS L H ⊓ residual H ≤
      A ⊔ Global.sourceS L H from inf_le_left.trans le_sup_right)]
  have hsmall := ChapterF.Source.MixedDGS.mixed_cubic_parabolic_core_derived_card_le_four
    hF11.swap e.quotient eU
  rw [hp] at hsmall
  change Nat.card (⁅Q,Q⁆ : Subgroup G) ≤ 4 at hsmall
  omega

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
