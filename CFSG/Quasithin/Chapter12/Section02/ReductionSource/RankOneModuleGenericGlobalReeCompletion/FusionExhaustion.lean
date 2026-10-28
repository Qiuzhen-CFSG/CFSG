module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.RootExhaustion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.RootFusion

/-!
# Chapter12 unrestricted Ree involution fusion

The prepared Chapter6 fusion theorem already proves both directions for native
root-class representatives. This application derives those memberships from
the actual order-two native preimages, so the Chapter12 consumer no longer
needs a separate class-membership premise. The full marking, both endpoint
orientations, actual quotient and original Sylow conventions are unchanged.

Source: Aschbacher--Smith F.4.27(3), F.4.30 and F.4.35, with the prepared
5.3.1--3 pair, printed pp.288--292 and 658--659 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ReeF4.EvenInvolutionGeometry

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Unrestricted endpoint involution fusion for the original prepared Ree
pair, with native class exhaustion discharged from the actual orders. -/
theorem rankOne_global_ree_root_endpoint_fusion_iff_of_involutions
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
    (hx : orderOf x.val = 2) (hy : orderOf y.val = 2)
    (hxm : R.extension.baseHom tx = x.val)
    (hym : R.extension.baseHom ty = y.val) :
    IsConj (R.endpointInverse i x) (R.endpointInverse j y) ↔ IsConj x.val y.val := by
  exact d.ree_root_endpoint_fusion_iff_of_involutions
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hp m hH he R x y hx hy hxm hym

/-- Unrestricted overlap involution fusion for the original prepared Ree pair. -/
theorem rankOne_global_ree_root_middle_fusion_iff_of_involutions
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
    (hx : orderOf x.val = 2) (hy : orderOf y.val = 2)
    (hxm : R.extension.baseHom tx = R.middleToCarrier x)
    (hym : R.extension.baseHom ty = R.middleToCarrier y) :
    IsConj x.val y.val ↔ IsConj (R.middleToCarrier x) (R.middleToCarrier y) := by
  exact d.ree_root_middle_fusion_iff_of_involutions
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hp m hH he R x y hx hy hxm hym

/-- Both directions of endpoint involution fusion, with native preimages
and class-membership hypotheses discharged. -/
theorem rankOne_global_ree_endpoint_involution_fusion_iff
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
    (hx : orderOf x.val = 2) (hy : orderOf y.val = 2) :
    IsConj (R.endpointInverse i x) (R.endpointInverse j y) ↔ IsConj x.val y.val := by
  exact d.ree_endpoint_involution_fusion_iff
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hp m hH he R x y hx hy

/-- Both directions of middle involution fusion, with native preimages
and class-membership hypotheses discharged. -/
theorem rankOne_global_ree_middle_involution_fusion_iff
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
    (hx : orderOf x.val = 2) (hy : orderOf y.val = 2) :
    IsConj x.val y.val ↔ IsConj (R.middleToCarrier x) (R.middleToCarrier y) := by
  exact d.ree_middle_involution_fusion_iff
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hp m hH he R x y hx hy

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
