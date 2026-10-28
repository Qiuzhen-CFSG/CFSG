module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialitySmallCompletion.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialitySmallCompletion

/-!
# The original Chapter12 triality GlobalExit

Apply the proved small-extension recognizer to the original whole-reduced
chosen-module input. The exponent stays n>1 and the comparison keeps its
mandatory reversal. The source extension, whole-normalizer marking and full
ambient bound are the only remaining realization inputs.

Source: Aschbacher--Smith 5.3.1--4, F.4.24 and 12.2.2, pp.658--659,287--288,795.
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
theorem rankOne_globalExit_of_triality_extension
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse))
    (E : SourceExtension m hm)
    (hext : Nonempty (RankTwoAmalgam.Iso
        (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam.reverse))
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    RankOneModule.GlobalExit G := by
  obtain ⟨_,_,_,_,_,ht⟩ := d.triality_extension_recognition
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he E hext horder
  exact Or.inl ⟨n,hn,ht⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
