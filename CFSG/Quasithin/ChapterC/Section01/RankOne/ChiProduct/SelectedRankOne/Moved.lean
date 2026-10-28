module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Kernel
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
/-!
# The literal moved module of the selected group

The alpha summand fixed by the residual is central in the selected group.
The remaining summand [U,O²(G)] is moved idempotently by the residual.
Consequently the full commutator of the C.1.17 omega-center span has exactly
that original moved image under the selected subgroup inclusion.

Source: Aschbacher–Smith C.1.26, p.132, natural-module identification.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem localV_selected_full_commutator (T U : Subgroup G)
    [U.Normal] [IsElementaryAbelian 2 U]
    (hgen : pResidual 2 G ⊔ T = ⊤)
    (hspan : U = normalClosure (omegaOneCenterAmbient T : Set G))
    (ha : thompsonAlpha T ≤ ⁅U,pResidual 2 G⁆ ⊔
      (thompsonAlpha T ⊓ centralizer (pResidual 2 G : Set G))) :
    (⁅GlaubermanNiles.localV (inclusion
      (show baumann T ≤ pResidual 2 G ⊔ baumann T from le_sup_right)),
      (⊤ : Subgroup (pResidual 2 G ⊔ baumann T : Subgroup G))⁆).map
      (pResidual 2 G ⊔ baumann T).subtype = ⁅U,pResidual 2 G⁆ := by
  let X := pResidual 2 G
  let W := ⁅U,X⁆
  let D := thompsonAlpha T ⊓ centralizer (X : Set G)
  let N := X ⊔ baumann T
  rw [map_commutator,localV_selected_baumann_eq_moved_sup_fixed T U X hgen hspan ha,
    ←MonoidHom.range_eq_map,range_subtype]
  change ⁅W ⊔ D,N⁆ = W
  have hWW : ⁅W,X⁆ = W := commutator_isPPerfect_idempotent X U
    (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
  apply le_antisymm
  · apply commutator_le.mpr
    intro v hv n hn
    obtain ⟨w,hw,d,hd,rfl⟩ := mem_sup_of_normal_left.mp hv
    have he : ⁅d,n⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (((fixed_alpha_central_selected T X) hd) n hn).symm
    rw [commutatorElement_mul_left_eq_conj_mul,he]
    simpa only [mul_one,mul_inv_cancel,mul_one,one_mul] using
      (commutator_le_left W N (commutator_mem_commutator hw hn))
  · exact hWW.symm.le.trans (commutator_mono
      (show W ≤ W ⊔ D from le_sup_left) (show X ≤ N from le_sup_left))
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
