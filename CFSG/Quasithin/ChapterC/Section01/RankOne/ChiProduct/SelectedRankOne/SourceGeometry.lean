module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Parabolic
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NormalLayerSource
/-!
# Original natural-layer source applied to the selected local group

The genuine Baumann theorem supplies the Sylow subgroup and alpha
decomposition. Their literal local-class consequences are assembled here:
minimal parabolic, characteristic two, elementary omega-center span, and
the exact action centralizer. All inputs remain the original reduced module,
normal SL₂ layer and its natural moved quotient; no local-class conclusion
is assumed.

Source: Aschbacher–Smith C.1.26, printed p.132, natural branch.
-/
public section
open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
theorem normal_layer_selected_geometry
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
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G) :
    let X := pResidual 2 G ⊔ baumann (T : Subgroup G)
    let b := inclusion (show baumann (T : Subgroup G) ≤ X from le_sup_right)
    (∃ S : Sylow 2 X, b.range = (S : Subgroup X) ∧ IsMinimalParabolicOver S ⊤) ∧
    generalizedFitting X = pCore 2 X ∧
    IsElementaryAbelian 2 (GlaubermanNiles.localV b) ∧
    GlaubermanNiles.localKernel b = (centralizer (U : Set G)).subgroupOf X ∧
    (GlaubermanNiles.localV b).map X.subtype =
      ⁅U,pResidual 2 G⁆ ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  obtain ⟨hs,ha⟩ := RankOneBaumann.normal_layer_moved_baumann_sylow_and_alpha
    T hP U hU hJ q hq hker L e hF f hf he hk
  have ha' : thompsonAlpha (T : Subgroup G) ≤ ⁅U,pResidual 2 G⁆ ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) :=
    ha.le.trans (sup_le_sup_right inf_le_left _)
  have hgen := pResidual_sup_sylow_eq_top T
  have hr := RankOneBaumann.residual_image_eq_normal_natural_layer T hP q hq L e hF
  let c := (MulEquiv.subgroupCongr hr).trans e
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  exact ⟨selected_baumann_minimal T hP U hU hJ q hq hker c hs,
    selected_baumann_fitting (T : Subgroup G) (pResidual 2 G) hgen hfit,
    localV_selected_baumann_elementary (T : Subgroup G) U (pResidual 2 G) hgen hspan ha',
    localKernel_selected_baumann (T : Subgroup G) U hU hgen hspan ha',
    localV_selected_baumann_eq_moved_sup_fixed (T : Subgroup G) U (pResidual 2 G) hgen hspan ha'⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
