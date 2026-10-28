module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NormalLayerSource
/-!
# The actual Baumann image in the selected rank-one layer

The natural moved quotient induces a faithful action of the entire original
centralizer quotient. The sharp SL₂ offender theorem then identifies the
Baumann image with its Sylow intersection with the marked normal layer.
This retains the given map and coordinate action for the C.1.17 actor.

Source: Aschbacher–Smith B.2.20, B.6.10 and C.1.26, pp.82,117,132.
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
theorem normal_layer_moved_baumann_image
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
      f v = 0 ↔ (v.toMul : G) ∈ centralizer (pResidual 2 G : Set G)) :
    (baumann (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ L := by
  let W := ⁅U,pResidual 2 G⁆
  have hCW : centralizer (W : Set G) = centralizer (U : Set G) := hU.centralizer_moved_eq U
  have hkerW : q.ker = centralizer (W : Set G) := hker.trans hCW.symm
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left U _)
  have hJW : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) :=
    fun h => hJ (h.trans_eq hCW)
  have heW : ∀ (a : L) v,
      f (NormalElementaryQuotient.representation W q hq hkerW (a : H) v) = N (e a) (f v) := by
    intro a v
    obtain ⟨g,hga⟩ := hq a
    have hgaL : q g ∈ L := hga.symm ▸ a.property
    have hv : NormalElementaryQuotient.representation W q hq hkerW (a : H) v =
        Additive.ofMul (MulAut.conjNormal g v.toMul) := by
      rw [←hga]
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply W q hq hkerW g v
    rw [hv]
    have hh := he g hgaL v
    have haa : (⟨q g,hgaL⟩ : L) = a := Subtype.ext hga
    rwa [haa] at hh
  have hkW : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation W q hq hkerW) ((pResidual 2 G).map q) := by
    ext v
    rw [NormalElementaryQuotient.mem_fixedSpace_image W q hq hkerW]
    exact hk v
  have hres := RankOneBaumann.residual_image_eq_normal_natural_layer T hP q hq L e hF
  have hcore : pCore 2 H = ⊥ := by
    let c := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 c,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hL : centralizer (L : Set H) ≤ L := by
    rw [←hres,map_pResidual_of_surjective 2 q hq]
    exact centralizer_pResidual_le_of_pCore_eq_bot hcore
  have hfaith : Function.Injective (MonoidHom.comp N e.toMonoidHom) := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact LinearMap.congr_fun hab v
  obtain ⟨ρ,hρ,heρ,hρL⟩ := BinaryOffender.exists_faithful_action_of_normal_layer_quotient
    (NormalElementaryQuotient.representation W q hq hkerW) L hL
    (MonoidHom.comp N e.toMonoidHom) hfaith f hf (hkW.trans (congrArg _ hres)) heW
  have hWT : W ≤ T := (IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal T
  exact (RankOneBaumann.thompson_baumann_images_of_semilinear_quotient T W q hq hkerW
    hWT hJW L e ρ hρ hρL hF f hf heρ).2
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
