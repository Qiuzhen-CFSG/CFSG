module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.RootExhaustion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.InvolutionReduction

/-!
# Chapter12 application of native Ree involution exhaustion

The original chosen-module input supplies the literal prepared whole-residual
pair. The Chapter6 application carries each original involution into the
positive native subgroup on the same full-normalizer marking, where the
concrete Ree coordinate proof gives its long-or-short root class. The result
keeps both source-comparison orientations and the original parameter equation.
It supplies involution-class exhaustion to later fusion arguments; it does not
assert the same-extension order comparison or final recognition.

Source: Aschbacher--Smith 5.3.1--3 and F.4.27(3), printed pp.658--659 and 288
of `refs/quasithin.pdf`; Guralnick--Malle, *Classification of 2F-modules, II*,
Lemma 8.8, internal p.57.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ReeF4.EvenInvolutionGeometry

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original Chapter12 Ree pair supplies root-class witnesses for the
native images of all original involutions, retaining its same full marking. -/
theorem rankOne_global_ree_full_extension_involution_root_classes
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
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    2*m+1 = n ∧ 0 < m ∧
      ∃ R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m,
        ∀ x : G, orderOf x = 2 →
          ∃ y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G),
            y.val ∈ (T : Subgroup G) ∧ IsConj x y.val ∧
              ∃ t : ReeF4.Model m,
                orderOf t = 2 ∧ t ∈ ReeF4.Parabolics.unipotent m ∧
                  R.middleToCarrier y = R.extension.baseHom t ∧
                    (IsLongRootInvolution t ∨ IsShortRootInvolution t) := by
  exact d.ree_full_extension_involution_root_classes
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hp m hH he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
