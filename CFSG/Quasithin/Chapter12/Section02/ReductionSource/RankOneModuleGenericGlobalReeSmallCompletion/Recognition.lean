module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeSmallCompletion.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeSmallCompletion.NativeCore

/-!
# The original Chapter12 Ree exit from the marked Weyl relation

Apply the conditional full-normalizer comparison to the original chosen
module. The genuine native group isomorphism supplies the Ree constructor
at the original exponent n=2m+1. The full extension, its actual compatible
comparison in either orientation, and the ambient order bound are retained.
The explicit marked eighth-power relation is still required; this is not
an unconditional prepared-row exit or a proof of F.4.24 recognition.

Source: Aschbacher–Smith 5.3.1–4, F.4.17,24 and 12.2.2,
printed pp.658–659,283,287–288,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ChapterF.SourceCompletion.GeneralReeExtension
open ChapterF.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Recognition at the original parameter from the literal marked local relation. -/
theorem rankOne_global_ree_recognition_of_weyl_relation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse))
    (E : SourceExtension m)
    (e : Global.ReeSmallCompletion.NormalizerComparison L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier)
    (hweyl : weylProduct E (Global.ReeSmallCompletion.normalizerCompletion L (residual H) E e)^8 = 1) :
    2*m+1 = n ∧ 0 < m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      Nat.card G = Nat.card E.carrier ∧ Nonempty (G ≃* ReeF4.Model m) :=
  d.ree_full_normalizers_recognition_of_weyl_relation
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he E e horder hweyl

/-- The conditional original-module exit, retaining its unresolved marked relation. -/
theorem rankOne_globalExit_of_ree_marked_weyl_relation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse))
    (E : SourceExtension m)
    (e : Global.ReeSmallCompletion.NormalizerComparison L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier)
    (hweyl : weylProduct E (Global.ReeSmallCompletion.normalizerCompletion L (residual H) E e)^8 = 1) :
    RankOneModule.GlobalExit G := by
  obtain ⟨hnm,hm,_,_,hi⟩ := D.rankOne_global_ree_recognition_of_weyl_relation
    h hmany hn hpsl hH d hp m he E e horder hweyl
  exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.ree_f4 m (by omega) hnm.symm hi⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
