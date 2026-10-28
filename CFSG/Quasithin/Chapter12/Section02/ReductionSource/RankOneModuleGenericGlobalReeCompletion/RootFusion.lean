module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.RootFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.Fusion

/-!
# Chapter12 converse fusion on the general Ree root classes

The original chosen module supplies the prepared rank-one input. The same
full Ree normalizer marking then identifies ambient and extension fusion
on either endpoint, and on their whole intersection, for native long- or
short-root representatives. Both comparison orientations are retained.

Native exhaustion remains explicit in the root-class membership hypotheses;
these local applications do not assert the final ambient recognition or
GlobalExit. Source: Aschbacher–Smith 5.3.1–3, F.4.27,30,35 and 12.2.2,
printed pp.658–659,288–292,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Converse fusion for native root-class representatives in the literal full endpoints of the original prepared pair. -/
theorem rankOne_global_ree_root_endpoint_fusion_iff
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
    (R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m)
    {i j : Bool} (x : R.extension.family i) (y : R.extension.family j)
    {tx ty : ReeF4.Model m}
    (hx : ReeF4.EvenInvolutionGeometry.IsLongRootInvolution tx ∨
      ReeF4.EvenInvolutionGeometry.IsShortRootInvolution tx)
    (hy : ReeF4.EvenInvolutionGeometry.IsLongRootInvolution ty ∨
      ReeF4.EvenInvolutionGeometry.IsShortRootInvolution ty)
    (hxm : R.extension.baseHom tx = x.val) (hym : R.extension.baseHom ty = y.val) :
    IsConj (R.endpointInverse i x) (R.endpointInverse j y) ↔ IsConj x.val y.val :=
  d.ree_root_endpoint_fusion_iff (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m he R x y hx hy hxm hym

/-- Converse fusion through the same whole common-normalizer map, including the original Sylow, for the two root classes. -/
theorem rankOne_global_ree_root_middle_fusion_iff
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
    (R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m)
    (x y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    {tx ty : ReeF4.Model m}
    (hx : ReeF4.EvenInvolutionGeometry.IsLongRootInvolution tx ∨
      ReeF4.EvenInvolutionGeometry.IsShortRootInvolution tx)
    (hy : ReeF4.EvenInvolutionGeometry.IsLongRootInvolution ty ∨
      ReeF4.EvenInvolutionGeometry.IsShortRootInvolution ty)
    (hxm : R.extension.baseHom tx = R.middleToCarrier x)
    (hym : R.extension.baseHom ty = R.middleToCarrier y) :
    IsConj x.val y.val ↔ IsConj (R.middleToCarrier x) (R.middleToCarrier y) :=
  d.ree_root_middle_fusion_iff (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m he R x y hx hy hxm hym

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
