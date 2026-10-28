module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOvercomponent
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The block-row overcomponent cores in the actual Chapter12 pair

Apply the L₃/Sp₄ branches of source 5.2.8 to K = O²(H), selected in the
original Chapter12 setup. Every local overcomponent of K has the same
embedded two-core, hence normalizes that core; the inclusion induces an
injective map of the literal core quotients. The quotient on K is PSL₂
at the original exponent. Neither relative core normality nor a quotient
embedding is an extra premise.

Both compatible orientations use the original S = O₂(N_G(L) ∩ H) and
whole overlap. The earlier preparation retains original uniqueness from
qt-d-1222-rankone-global-uniqueness and exhaustive F.1.12 comparison.
The remaining 5.2.8 overcomponent classification and ambient completion
recognition stay with the generic/global owner; this is not GlobalExit.
Source: Aschbacher–Smith 5.2.8, printed p.652, and the Chapter12 application
on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Discharge the core equality and quotient embedding in the block branches
of 5.2.8 for the original prepared whole-residual pair. The overcomponent
need not be assumed to normalize K or its core. -/
theorem rankOne_global_block_overcomponent_quotient
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B J : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he :
      (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (LinearThree.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (LinearThree.amalgam F).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (SymplecticFour.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (SymplecticFour.amalgam F).reverse)))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H ≤ J) :
    J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∧
      ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^n) ∧
      ∃ f : (residual H ⧸ pCore 2 (residual H)) →* (J ⧸ pCore 2 J),
        Function.Injective f ∧ ∀ x : residual H,
          f (QuotientGroup.mk' (pCore 2 (residual H)) x) =
            QuotientGroup.mk' (pCore 2 J) (inclusion hKJ x) :=
  d.block_overcomponent_quotient (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp F hm hF he hJ hKJ

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
