module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.Spaces
/-!
# A nonzero normal module commutator is the short block module

Subnormal p-perfect core action puts [U,K] inside U(K). Its action is
idempotent, so a nonzero commutator cannot be centralized by K. The short
normal-layer dichotomy therefore identifies it with the entire U(K).
This discharges actual support in the given reduced module.

Source: Aschbacher–Smith C.1.27, p.133, and C.1.7–8.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
variable {G : Type*} [Group G] [Finite G]

theorem blockU_eq_nontrivial_normal_module_commutator
    (K U : Subgroup G) (hK : IsBlock K) [U.Normal] [IsElementaryAbelian 2 U]
    (hne : ⁅U,K⁆ ≠ ⊥) : (blockU K).map K.subtype = ⁅U,K⁆ := by
  let W := ⁅U,K⁆
  have hWU : W ≤ (blockU K).map K.subtype :=
    commutator_le_core_commutator_of_isSubnormal K U hK.subnormal hK.short.twoPerfect
      (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
  have hWK : W ≤ K := hWU.trans (map_subtype_le _)
  let V := W.subgroupOf K
  let : V.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right U K)
  have hVU : V ≤ blockU K := by
    intro v hv
    obtain ⟨u,hu,he⟩ := hWU hv
    exact (Subtype.ext he : u=v) ▸ hu
  rcases short_normal_layer_dichotomy hK.short V hVU with hc | he
  · have hcomm : ⁅W,K⁆ = W := commutator_isPPerfect_idempotent K U hK.short.twoPerfect
      (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
    have hfix : W ≤ centralizer (K : Set G) := by
      intro w hw k hk
      exact congrArg Subtype.val (mem_center_iff.mp (hc (show (⟨w,hWK hw⟩:K) ∈ V from hw)) ⟨k,hk⟩)
    exact (hne (hcomm.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hfix))).elim
  · have hm := congrArg (map K.subtype) he
    rw [map_subgroupOf_eq_of_le hWK] at hm
    exact hm.symm
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
