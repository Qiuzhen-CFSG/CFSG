module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialitySmallCompletion.NativeApartment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionTriality

/-!
# The original Chapter12 native triality subgroup order

The original chosen-module hypotheses retain the complete normalizer diagram,
whole-residual branch, source reversal, and exponent n=m>1. The full extension
order bound now forces the exact native subgroup order and native diameter
six. The marked sixth-power defect lies in the native Borel; group recognition
and GlobalExit remain further obligations.

Source: Aschbacher--Smith 5.3.1--4, F.4.24 and 12.2.2, pp.658--659,287--288,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ChapterF.SourceCompletion.TrialityNonbinary
open ChapterF.SourceCompletion
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

theorem rankOne_global_triality_full_normalizers_native_apartment
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
    m = n ∧ 1 < m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      Nat.card G = Nat.card E.carrier ∧
      ∃ c : Completion E (normalizer (L : Set G) ⊔ normalizer (residual H : Set G) : Subgroup G),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        (nativeCore E c).Normal ∧
        Nat.card (nativeCore E c) = Nat.card (_root_.Triality.Standard.BinaryCarrier m hm) ∧
        (nativeCompletion E c).left.range ⊓ (nativeCompletion E c).right.range =
          (nativeCompletion E c).middle.range ∧
        (∀ v w, (graph (nativeCompletion E c).cosetFamily).dist v w ≤ 6) ∧
        ∃ b : _root_.Triality.Standard.Parabolics.borel (_root_.Triality.Standard.binaryParameters m hm),
          c.left (E.nativeLeft ⟨b.val,_root_.Triality.Standard.Parabolics.borel_le_parabolic _ .arms b.property⟩) =
            (c.left (E.nativeLeft (reflection m hm .arms)) *
              c.right (E.nativeRight (reflection m hm .central)))^6 :=
  d.triality_full_normalizers_native_apartment
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he E hext horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
