module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.NativeAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.LocalActions

/-!
# The Chapter12 Ree pair and its native common-normalizer action

The original Hypothesis 12.2.1, chosen module, actual PSL₂ quotient and
prepared whole-residual comparison yield a faithful action of the entire
normalizer intersection on the complete native Ree group. Both parabolic
restrictions and the whole Borel retain the original conjugation marking.
This applies at every positive parameter, including q=8, in either supplied
comparison orientation and introduces no native extension premise.

The simultaneous full-normalizer diagram, ambient centralizer and order
arguments, and the final GlobalExit are further source obligations.
Source: Aschbacher–Smith 5.3.2, F.4.3 and 12.2.2,
printed pp.659,274,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original whole normalizer intersection acts faithfully on the full
native Ree model, with both parabolic restrictions and the entire Borel retained. -/
theorem rankOne_global_ree_native_intersection_action
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
    ∃ e : RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse,
    ∃ (a : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
        RankTwoAmalgam.Iso (ReeFour.amalgam m).reverse (ReeFour.amalgam m).reverse)
      (σ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
        MulAut (ReeF4.Model m)),
      Function.Injective σ ∧
      (∀ g x, (e.left.symm ((a g).left (e.left x)) : G) =
        (g : G)*(x : G)*(g : G)⁻¹) ∧
      (∀ g x, (e.right.symm ((a g).right (e.right x)) : G) =
        (g : G)*(x : G)*(g : G)⁻¹) ∧
      (∀ g x, (e.middle.symm ((a g).middle (e.middle x)) : G) =
        (g : G)*(x : G)*(g : G)⁻¹) ∧
      (∀ g (x : ReeF4.Parabolics.parabolic m .linear),
        σ g x.val=((a g).left x).val) ∧
      (∀ g (x : ReeF4.Parabolics.parabolic m .suzuki),
        σ g x.val=((a g).right x).val) ∧
      (∀ g (x : ReeF4.Parabolics.borel m),
        σ g x.val=((a g).middle x).val) := by
  exact d.ree_native_intersection_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
