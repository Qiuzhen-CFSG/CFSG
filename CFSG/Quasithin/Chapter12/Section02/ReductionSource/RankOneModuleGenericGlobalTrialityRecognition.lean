module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityShortCentralizer.Application

/-!
# The complete prepared Chapter 12 triality branch

The original chosen module supplies the generic input for the completed
triality order and recognition argument. Both catalogue orientations are
handled, and the output retains an actual isomorphism with the native
triality carrier at m = n > 1. The global exit uses that original exponent.
The same-extension order equality is also exposed for the given reversed
comparison, with no additional centralizer or order premise.

The preparation and concrete comparison remain the source inputs; this
module does not assert exhaustive classification of selected perfect factors.
Source: Aschbacher--Smith F.4.40--44, printed pp.294--296, 5.3.3--4, p.659,
and the Chapter 12 application, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Triality.Standard
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.SourceCompletion.TrialityNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original chosen-module setup gives order equality for its fixed
full-normalizer extension and supplied reversed comparison. -/
theorem rankOne_global_triality_ambient_order
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (nativeAmalgam m hm).reverse) :
    Nat.card G = Nat.card (d.trialityNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e).extension.carrier :=
  d.triality_ambient_order (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e

/-- An actual comparison in either orientation recognizes original G as the
native triality group, at its unchanged original exponent greater than one. -/
theorem rankOne_global_triality_ambient_recognition
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (nativeAmalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (nativeAmalgam m hm).reverse)) :
    m = n ∧ 1 < m ∧ Nonempty (G ≃* BinaryCarrier m hm) ∧
      ClassificationModels.IsRankTwoModel G n :=
  d.triality_ambient_recognition (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm he

/-- The completed triality comparison branch supplies the strict rank-two
global exit with no centralizer, extension, order or recognition callback. -/
theorem rankOne_globalExit_of_triality_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (nativeAmalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (nativeAmalgam m hm).reverse)) :
    RankOneModule.GlobalExit G := by
  have hr := D.rankOne_global_triality_ambient_recognition h hmany hn hpsl hH d hp m hm he
  exact Or.inl ⟨n,hn,hr.2.2.2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
