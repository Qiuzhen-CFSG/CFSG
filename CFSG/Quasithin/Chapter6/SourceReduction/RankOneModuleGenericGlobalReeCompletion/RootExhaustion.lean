module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.InvolutionReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.RootFusion
public import Theory.SpecificGroups.ReeF4.SourceCompletion.RootExhaustion

/-!
# Root-class witnesses on the original Ree Sylow marking

The prepared full-overlap construction already represents each original
ambient involution by an involution in the native positive subgroup, through
the same original Sylow and common-normalizer marking. The native coordinate
exhaustion therefore supplies its long-or-short root witness without changing
the representative or comparison orientation. This closes the F.4.27
class-membership premise for the prepared row. The odd outer quotient gives
native preimages of every endpoint involution, so the existing root-fusion
comparison applies on both full endpoints and the whole common normalizer.
Order comparison and ambient recognition remain separate obligations.

Source: Aschbacher--Smith 5.3.1--3 and F.4.27(3), printed pp.658--659 and 288
of `refs/quasithin.pdf`; Guralnick--Malle, *Classification of 2F-modules, II*,
Lemma 8.8, internal p.57.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ReeF4.EvenInvolutionGeometry

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include d h hp hH he

/-- Every original ambient involution has a Sylow representative whose native
image in the same prepared extension is in one of the two actual root classes.
The parameter equation and positive parameter are retained from the original
full-normalizer marking construction. -/
theorem Preparation.ree_full_extension_involution_root_classes :
    2*m+1 = n ∧ 0 < m ∧
      ∃ D : ReeNormalizerMarking L (residual H) (sourceS L H) m,
        ∀ x : G, orderOf x = 2 →
          ∃ y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G),
            y.val ∈ (T : Subgroup G) ∧ IsConj x y.val ∧
              ∃ t : ReeF4.Model m,
                orderOf t = 2 ∧ t ∈ ReeF4.Parabolics.unipotent m ∧
                  D.middleToCarrier y = D.extension.baseHom t ∧
                    (IsLongRootInvolution t ∨ IsShortRootInvolution t) := by
  obtain ⟨hn, hm, D, hrep⟩ :=
    d.ree_full_extension_involution_normal_forms h hp m hH he
  refine ⟨hn, hm, D, ?_⟩
  intro x hx
  obtain ⟨y, t, p, r, hy, hxy, ht, htu, hmark, _, _, _⟩ := hrep x hx
  have hm' : 1 ≤ m := by omega
  exact ⟨y, hy, hxy, t, ht, htu, hmark,
    ReeF4.SourceCompletion.involution_root_classes m hm' t ht⟩

include hH he

/-- Involution fusion through both full endpoints follows without native
root-class membership hypotheses: injectivity of the same model embedding
transfers the endpoint orders to native involutions, and native exhaustion
supplies the two root-class witnesses. -/
theorem Preparation.ree_root_endpoint_fusion_iff_of_involutions
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    {i j : Bool} (x : D.extension.family i) (y : D.extension.family j)
    {tx ty : ReeF4.Model m}
    (hx : orderOf x.val = 2) (hy : orderOf y.val = 2)
    (hxm : D.extension.baseHom tx = x.val)
    (hym : D.extension.baseHom ty = y.val) :
    IsConj (D.endpointInverse i x) (D.endpointInverse j y) ↔ IsConj x.val y.val := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  have hi : Function.Injective D.extension.baseHom :=
    (MonoidHom.injective_codRestrict _ _ _).mpr (ReeF4.SmallCompletion.conj_injective m hm)
  have htx : orderOf tx = 2 := by
    calc
      orderOf tx = orderOf (D.extension.baseHom tx) :=
        (orderOf_injective D.extension.baseHom hi tx).symm
      _ = orderOf x.val := congrArg orderOf hxm
      _ = 2 := hx
  have hty : orderOf ty = 2 := by
    calc
      orderOf ty = orderOf (D.extension.baseHom ty) :=
        (orderOf_injective D.extension.baseHom hi ty).symm
      _ = orderOf y.val := congrArg orderOf hym
      _ = 2 := hy
  exact d.ree_root_endpoint_fusion_iff h hH hp m he D x y
    (ReeF4.SourceCompletion.involution_root_classes m (by omega) tx htx)
    (ReeF4.SourceCompletion.involution_root_classes m (by omega) ty hty) hxm hym

/-- The same unrestricted involution-fusion equivalence through the entire
original common-normalizer map. In particular it applies to the original
Sylow representatives used by the source comparison. -/
theorem Preparation.ree_root_middle_fusion_iff_of_involutions
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (x y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    {tx ty : ReeF4.Model m}
    (hx : orderOf x.val = 2) (hy : orderOf y.val = 2)
    (hxm : D.extension.baseHom tx = D.middleToCarrier x)
    (hym : D.extension.baseHom ty = D.middleToCarrier y) :
    IsConj x.val y.val ↔ IsConj (D.middleToCarrier x) (D.middleToCarrier y) := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  have hi : Function.Injective D.extension.baseHom :=
    (MonoidHom.injective_codRestrict _ _ _).mpr (ReeF4.SmallCompletion.conj_injective m hm)
  have hti : Function.Injective D.middleToCarrier :=
    (inclusion_injective (inf_le_left.trans D.extension.left_le)).comp D.full.middle.injective
  have htx : orderOf tx = 2 := by
    calc
      orderOf tx = orderOf (D.extension.baseHom tx) :=
        (orderOf_injective D.extension.baseHom hi tx).symm
      _ = orderOf (D.middleToCarrier x) := congrArg orderOf hxm
      _ = orderOf x := orderOf_injective D.middleToCarrier hti x
      _ = orderOf x.val := (Subgroup.orderOf_coe x).symm
      _ = 2 := hx
  have hty : orderOf ty = 2 := by
    calc
      orderOf ty = orderOf (D.extension.baseHom ty) :=
        (orderOf_injective D.extension.baseHom hi ty).symm
      _ = orderOf (D.middleToCarrier y) := congrArg orderOf hym
      _ = orderOf y := orderOf_injective D.middleToCarrier hti y
      _ = orderOf y.val := (Subgroup.orderOf_coe y).symm
      _ = 2 := hy
  exact d.ree_root_middle_fusion_iff h hH hp m he D x y
    (ReeF4.SourceCompletion.involution_root_classes m (by omega) tx htx)
    (ReeF4.SourceCompletion.involution_root_classes m (by omega) ty hty) hxm hym

/-- Both fusion directions on the entire full endpoints. The odd outer
quotient supplies native preimages of every involution, so neither preimages
nor root-class memberships remain premises. -/
theorem Preparation.ree_endpoint_involution_fusion_iff
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    {i j : Bool} (x : D.extension.family i) (y : D.extension.family j)
    (hx : orderOf x.val = 2) (hy : orderOf y.val = 2) :
    IsConj (D.endpointInverse i x) (D.endpointInverse j y) ↔ IsConj x.val y.val := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  obtain ⟨tx, _, hxm⟩ := GeneralReeFour.extension_involution_native D.extension hm x.val hx
  obtain ⟨ty, _, hym⟩ := GeneralReeFour.extension_involution_native D.extension hm y.val hy
  exact d.ree_root_endpoint_fusion_iff_of_involutions h hp m hH he D x y hx hy hxm hym

/-- Both fusion directions through the entire common normalizer, including
the original Sylow, without specifying native preimages. -/
theorem Preparation.ree_middle_involution_fusion_iff
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (x y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    (hx : orderOf x.val = 2) (hy : orderOf y.val = 2) :
    IsConj x.val y.val ↔ IsConj (D.middleToCarrier x) (D.middleToCarrier y) := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  have hi : Function.Injective D.middleToCarrier :=
    (inclusion_injective (inf_le_left.trans D.extension.left_le)).comp D.full.middle.injective
  have hxE : orderOf (D.middleToCarrier x) = 2 :=
    (orderOf_injective _ hi x).trans ((Subgroup.orderOf_coe x).symm.trans hx)
  have hyE : orderOf (D.middleToCarrier y) = 2 :=
    (orderOf_injective _ hi y).trans ((Subgroup.orderOf_coe y).symm.trans hy)
  obtain ⟨tx, _, hxm⟩ := GeneralReeFour.extension_involution_native D.extension hm _ hxE
  obtain ⟨ty, _, hym⟩ := GeneralReeFour.extension_involution_native D.extension hm _ hyE
  exact d.ree_root_middle_fusion_iff_of_involutions h hp m hH he D x y hx hy hxm hym

/-- Literal full-left-normalizer fusion: this discharges the endpoint-fusion
premise of the original short-marker extremality selection. -/
theorem Preparation.ree_left_involution_fusion_iff
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (x y : normalizer (L : Set G))
    (hx : orderOf x.val = 2) (hy : orderOf y.val = 2) :
    IsConj x.val y.val ↔ IsConj (D.leftToCarrier x) (D.leftToCarrier y) := by
  have hxE : orderOf (D.leftToCarrier x) = 2 :=
    (orderOf_injective _ D.leftToCarrier_injective x).trans
      ((Subgroup.orderOf_coe x).symm.trans hx)
  have hyE : orderOf (D.leftToCarrier y) = 2 :=
    (orderOf_injective _ D.leftToCarrier_injective y).trans
      ((Subgroup.orderOf_coe y).symm.trans hy)
  have hf := d.ree_endpoint_involution_fusion_iff h hp m hH he D
    (i := false) (j := false)
    ⟨D.leftToCarrier x, (D.full.left x).property⟩
    ⟨D.leftToCarrier y, (D.full.left y).property⟩ hxE hyE
  rw [D.endpointInverse_left, D.endpointInverse_left] at hf
  exact hf


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
