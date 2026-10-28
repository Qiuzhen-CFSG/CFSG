module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtension.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialitySmallCompletion.Recognition

/-!
# The chosen-module exit from the constructed triality extension

For the original whole-reduced module and residual, the pure comparison
constructs the full-normalizer extension internally. Its same-carrier order
bound is the only additional premise of the accepted GlobalExit consumer.

Source: Aschbacher–Smith 5.3.2, F.4.24 and 12.2.2, pp.659,287–288,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ChapterF.SourceCompletion.TrialityNonbinary ChapterF.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal chosen-module triality exit retains the original exponent,
whole residual and whole-normalizer extension order. -/
theorem rankOne_globalExit_of_triality_prepared_extension_order
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (nativeAmalgam m hm).reverse)
    (horder : Nat.card G ≤ Nat.card
      (d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
        hH hp m hm e).extension.carrier) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_triality_extension h hmany hn hpsl hH d hp m hm (Or.inr ⟨e⟩)
    (d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp m hm e).extension
    (Or.inr ⟨(d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp m hm e).comparison⟩) horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
