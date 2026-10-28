module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedSupport
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
/-!
# Kernel and moved group of the selected component module

The central alpha summand changes neither the local action kernel nor the
full moved subgroup. The original local module, its subgroup inclusion, and
the selected component remain literal throughout these two identities.

Source: Aschbacher–Smith C.1.17 and C.1.26, printed pp.126 and132.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem localKernel_factor_baumann
    (T U L : Subgroup G)
    (hv : (GlaubermanNiles.localV (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right))).map
      (L ⊔ baumann T).subtype = ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    GlaubermanNiles.localKernel (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right)) =
      (centralizer ((⁅U,L⁆ : Subgroup G) : Set G)).subgroupOf (L ⊔ baumann T) := by
  let N := L ⊔ baumann T
  let b := inclusion (show baumann T ≤ N from le_sup_right)
  have hw : ⁅U,L⁆ ≤ (GlaubermanNiles.localV b).map N.subtype := hv.symm ▸ le_sup_left
  ext x
  constructor
  · intro hx w hw'
    obtain ⟨v,hv',he⟩ := hw hw'
    have hh := congrArg (fun a : N => (a : G)) (hx v hv')
    change (v:G) = w at he
    change w*(x:G)=(x:G)*w
    rw [←he]
    exact hh
  · intro hx v hv'
    apply Subtype.ext
    have hjoin : ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G)) ≤
        centralizer ({(x:G)} : Set G) := by
      apply sup_le
      · intro w hw z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact (hx w hw).symm
      · intro d hd z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact fixed_alpha_central_selected T L hd x x.property
    have hh : (v:G) ∈ ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G)) :=
      hv ▸ mem_map_of_mem N.subtype hv'
    exact (hjoin hh x (Set.mem_singleton _)).symm

theorem localV_factor_full_commutator
    (T U L : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hL : IsPPerfect 2 L)
    (hUL : U ≤ normalizer (L : Set G)) (hBL : baumann T ≤ normalizer (L : Set G))
    (hv : (GlaubermanNiles.localV (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right))).map
      (L ⊔ baumann T).subtype = ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    (⁅GlaubermanNiles.localV (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right)),
      (⊤ : Subgroup (L ⊔ baumann T : Subgroup G))⁆).map (L ⊔ baumann T).subtype = ⁅U,L⁆ := by
  let W := ⁅U,L⁆
  let D := thompsonAlpha T ⊓ centralizer (L : Set G)
  let N := L ⊔ baumann T
  have hWN : W ≤ N := (le_normalizer_iff_commutator_le_right.mp hUL).trans le_sup_left
  have hEN : thompsonAlpha T ≤ N := by
    rw [←baumann_omega_eq_alpha T]
    intro x hx
    exact (show baumann T ≤ N from le_sup_right) ((mem_omegaOneCenterAmbient_iff (baumann T) x).mp hx).1
  have hDN : D ≤ N := inf_le_left.trans hEN
  have hNW : N ≤ normalizer (W : Set G) := by
    apply sup_le (normalizer_commutator_ge_right U L)
    intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅U,L⁆ : Subgroup G).map (MulAut.conj b).toMonoidHom = ⁅U,L⁆
    have hl : L.map (MulAut.conj b).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp (hBL hb)
    have hu : U.map (MulAut.conj b).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp (U.normalizer_eq_top.symm ▸ mem_top b)
    rw [map_commutator,hl,hu]
  have hWcomm : ⁅W,N⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hNW
  have hDcomm : ⁅D,N⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (fixed_alpha_central_selected T L)
  have hpre : W ⊔ D ≤ commutatorPreimage N N W := sup_le
    (le_commutatorPreimage hWN hWcomm) (le_commutatorPreimage hDN (hDcomm.le.trans bot_le))
  rw [map_commutator,hv,←MonoidHom.range_eq_map,range_subtype]
  apply le_antisymm ((commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le N N W hNW))
  have hi : ⁅W,L⁆ = W := commutator_isPPerfect_idempotent L U hL
    (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
  exact hi.symm.le.trans (commutator_mono le_sup_left le_sup_left)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
