module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.SourceGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Images
/-!
# The selected group's original centralizer quotient

The restricted quotient map has precisely the local C.1.17 kernel. The
Baumann image theorem identifies its image with the given normal SL₂ layer.
The resulting equivalence records its value on every original group element,
so subsequent natural-module transport uses the same action and quotient.

Source: Aschbacher–Smith C.1.26, printed p.132.
-/
public section
open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB
variable {G H : Type*} [Group G] [Group H]

theorem exists_selectedStar_equiv {B : Type*} [Group B]
    (X : Subgroup G) (b : B →* X) (q : G →* H) (L : Subgroup H)
    (hk : GlaubermanNiles.localKernel b = q.ker.subgroupOf X)
    (hL : X.map q = L) :
    ∃ c : GlaubermanNiles.LocalStar b ≃* L, ∀ x : X,
      (c (QuotientGroup.mk' (GlaubermanNiles.localKernel b) x) : H) = q x := by
  let f := q.subgroupMap X
  have hf : f.ker = GlaubermanNiles.localKernel b := by
    rw [hk]
    ext x
    exact Subtype.ext_iff
  let c := ((QuotientGroup.quotientMulEquivOfEq hf.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective X))).trans
    (MulEquiv.subgroupCongr hL)
  exact ⟨c,fun _ => rfl⟩
variable {F : Type*} [Finite G] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
theorem normal_layer_selectedStar_equiv
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal] (e : L ≃* D) (hF : 2 < Nat.card F)
    (f : Additive (⁅U,pResidual 2 G⁆ : Subgroup G) →ₗ[ZMod 2] (Fin 2 → F))
    (hf : Function.Surjective f)
    (he : ∀ (g : G) (hg : q g ∈ L) (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f (Additive.ofMul (MulAut.conjNormal g v.toMul)) = N (e ⟨q g,hg⟩) (f v))
    (hk : ∀ (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f v = 0 ↔ (v.toMul : G) ∈ centralizer (pResidual 2 G : Set G))
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let X := pResidual 2 G ⊔ baumann (T : Subgroup G)
    let b := inclusion (show baumann (T : Subgroup G) ≤ X from le_sup_right)
    ∃ c : GlaubermanNiles.LocalStar b ≃* L, ∀ x : X,
      (c (QuotientGroup.mk' (GlaubermanNiles.localKernel b) x) : H) = q x := by
  have hb := normal_layer_moved_baumann_image T hP U hU hJ q hq hker L e hF f hf he hk
  have hr := RankOneBaumann.residual_image_eq_normal_natural_layer T hP q hq L e hF
  have hX : (pResidual 2 G ⊔ baumann (T : Subgroup G)).map q = L := by
    rw [Subgroup.map_sup,hr,hb,sup_eq_left.mpr inf_le_right]
  obtain ⟨_,ha⟩ := RankOneBaumann.normal_layer_moved_baumann_sylow_and_alpha
    T hP U hU hJ q hq hker L e hF f hf he hk
  have ha' : thompsonAlpha (T : Subgroup G) ≤ ⁅U,pResidual 2 G⁆ ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) :=
    ha.le.trans (sup_le_sup_right inf_le_left _)
  have hkb := localKernel_selected_baumann (T : Subgroup G) U hU
    (pResidual_sup_sylow_eq_top T) hspan ha'
  rw [←hker] at hkb
  exact exists_selectedStar_equiv _ _ q L hkb hX
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
