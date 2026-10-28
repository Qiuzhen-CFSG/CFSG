module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicReducedAction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Moved
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.CubicResidual
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The literal Baumann omega-center span in the selected cubic route

The original reduced module at Sylow index three constructs the Baumann
Sylow and alpha bound. The field-free localV comparison then computes the
canonical local omega-center span, its elementary structure, its exact
two-core centralizer, and the original moved support under inclusion.
Source: Aschbacher–Smith C.1.21(1),(4), printed pp.128–129.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB ChiProduct.SelectedRankOne
variable {G : Type*} [Group G] [Finite G]

private theorem normal_supplement_sylow_index (T : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (S : Sylow 2 N) (hST : (S : Subgroup N).map N.subtype ≤ T)
    (hgen : N ⊔ (T : Subgroup G) = ⊤) :
    (S : Subgroup N).index = (T : Subgroup G).index := by
  have hle : (S : Subgroup N) ≤ (T : Subgroup G).subgroupOf N :=
    fun s hs => hST (mem_map_of_mem N.subtype hs)
  have he := S.is_maximal' T.isPGroup'.comap_subtype hle
  have hmap : (S : Subgroup N).map N.subtype = N ⊓ (T : Subgroup G) := by
    rw [←he,map_comap_eq,range_subtype,inf_comm]
  have hc : Nat.card (N ⊓ (T : Subgroup G) : Subgroup G) = Nat.card S := by
    rw [←hmap,card_map_of_injective N.subtype_injective]
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes N (T : Subgroup G) le_normalizer_of_normal
  rw [hgen,card_top,hc] at hp
  have hN := (S : Subgroup N).index_mul_card
  have hT := (T : Subgroup G).index_mul_card
  have heq : (S : Subgroup N).index * (Nat.card S * Nat.card T) =
      (T : Subgroup G).index * (Nat.card S * Nat.card T) := by nlinarith
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos) heq

/-- The canonical local span for the actual Baumann Sylow has the original
moved support and the exact intrinsic two-core kernel. -/
theorem cubic_baumann_span (T : Sylow 2 G)
    (hi : (T : Subgroup G).index = 3)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G) :
    let N := pResidual 2 G ⊔ baumann (T : Subgroup G)
    let e := inclusion (show baumann (T : Subgroup G) ≤ N from le_sup_right)
    (∃ S : Sylow 2 N, e.range = (S : Subgroup N) ∧ (S : Subgroup N).index = 3) ∧
      generalizedFitting N = pCore 2 N ∧
      IsElementaryAbelian 2 (GlaubermanNiles.localV e) ∧
      GlaubermanNiles.localKernel e = pCore 2 N ∧
      (⁅GlaubermanNiles.localV e,(⊤ : Subgroup N)⁆).map N.subtype = ⁅U,pResidual 2 G⁆ := by
  let B := baumann (T : Subgroup G)
  let N := pResidual 2 G ⊔ B
  let e := inclusion (show B ≤ N from le_sup_right)
  have hgen := pResidual_sup_sylow_eq_top T
  obtain ⟨hb,ha⟩ := reduced_index_three_moved_baumann T hi U hU hJ
  have hkU := (reduced_index_three_action T hi U hU hJ).2.1
  let : N.Normal := baumann_residual_join_normal (T : Subgroup G) (pResidual 2 G) hgen
  have hBT : B ≤ (T : Subgroup G) := inf_le_left
  obtain ⟨S,hS⟩ := hb
  have hST : (S : Subgroup N).map N.subtype ≤ T := hS.le.trans hBT
  have hNT : N ⊔ (T : Subgroup G) = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le_sup le_sup_left le_rfl
  have hS' : e.range = (S : Subgroup N) := by
    apply map_injective N.subtype_injective
    rw [hS,MonoidHom.map_range,show N.subtype.comp e = B.subtype from rfl,range_subtype]
  have hcore : (pCore 2 G).subgroupOf N = pCore 2 N := by
    refine le_antisymm ?_ ?_
    · exact le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
    have hh : (pCore 2 N).map N.subtype ≤ pCore 2 G := le_sSup
      ⟨inferInstance,pCore_isPGroup.map N.subtype⟩
    exact fun n hn => hh (mem_map_of_mem N.subtype hn)
  refine ⟨⟨S,hS',by rw [normal_supplement_sylow_index T N S hST hNT,hi]⟩,?_,
    localV_selected_baumann_elementary (T : Subgroup G) U (pResidual 2 G) hgen hspan ha,?_,
    localV_selected_full_commutator (T : Subgroup G) U hgen hspan ha⟩
  · exact (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (normal_core_selfCentralizing ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit) N)
  · rw [localKernel_selected_baumann (T : Subgroup G) U hU hgen hspan ha,hkU,hcore]
end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
