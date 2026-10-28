module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialitySmallCompletion.NativeLift
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionTriality

/-!
# Native lifts for the original Chapter12 triality comparison

The whole-reduced chosen-module input supplies the original preparation.
Compatible source conjugation extends through the literal reversed comparison
on both native parabolics, before any ambient extension-order argument.
Source: Aschbacher--Smith 5.3.2 and 12.2.2, pp.659,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.SourceCompletion.TrialityNonbinary
open _root_.Triality.Standard
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Lift both compatible original conjugation maps at m=n>1. -/
theorem rankOne_global_triality_native_conjugation_lift
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      (nativeAmalgam m hm).reverse)
    (a : RankTwoAmalgam.Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)))
    (g : G)
    (hl : ∀ x, (a.left x).val=g*x.val*g⁻¹)
    (hr : ∀ x, (a.right x).val=g*x.val*g⁻¹) :
    m=n ∧ 1<m ∧ ∃ f : MulAut (BinaryCarrier m hm),
      (∀ x, f (e.left x).val =
        (e.left ⟨g*x.val*g⁻¹,by rw [←hl x]; exact (a.left x).property⟩).val) ∧
      (∀ x, f (e.right x).val =
        (e.right ⟨g*x.val*g⁻¹,by rw [←hr x]; exact (a.right x).property⟩).val) :=
  d.triality_native_conjugation_lift (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp m hm e a g hl hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
