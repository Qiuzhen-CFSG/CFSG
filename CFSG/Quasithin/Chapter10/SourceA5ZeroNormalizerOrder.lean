module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroModuleOrder
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.FivePairSource
/-!
# Orders in the original zero-center normalizer calculation

The faithful paired natural action identifies the original local quotient with
S₅ wreath C₂. Its elementary kernel has order 256, so the original Sylow has
order 32768. The four-dihedral Baumann subgroup has order 4096. These orders
supply the eight-element image of the canonical central-enlargement action.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false
/-- The original Sylow subgroup has order 2¹⁵. -/
theorem source_a5_zero_sylow_card
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Nat.card T = 32768 := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  obtain ⟨d,c,hex,_,_⟩ := source_a5_paired_baumann_action D e hn hout
  obtain ⟨hcY,ρ,hfaith,_,hnat⟩ := c.source_full_faithful_action S
    (source_a5_minimal_parabolic D e hn) U hU
    (source_local_thompson_not_centralizes D hout) q hq hk d
  obtain ⟨t,ht,_⟩ := hex
  obtain ⟨ew,_,_⟩ := ChapterB.source_pair_wreath_of_faithful_action Y (α.comp Y.subtype)
    d c hcY ρ hfaith hnat ⟨t,ht⟩
  have hquot : Nat.card (H ⧸ C) = 28800 := by
    rw [Nat.card_congr ew.toEquiv]
    norm_num [BinaryPermutation.FivePair.Wreath, RegularWreathProduct.card,
      BinaryPermutation.FivePair.C2,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hc : Nat.card C = 256 := by
    rw [show C = U from source_a5_zero_centralizer_local_module_centralizer D e hn hout hz]
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (D.module_le_core.trans (pCoreIn_le 2 H))).toEquiv,source_a5_zero_module_card D e hn hout hz]
  have hH : Nat.card H = 7372800 := by
    have hh := C.card_mul_index
    rw [C.index_eq_card,hquot,hc] at hh
    omega
  have hs : Nat.card S = 32768 := by
    rw [S.card_eq_multiplicity,hH]
    decide +kernel
  exact (Nat.card_congr (subgroupOfEquivOfLe
    (show (T : Subgroup G) ≤ H from le_sup_right)).toEquiv).symm.trans hs
/-- The original four-dihedral Baumann subgroup has order 2¹². -/
theorem source_a5_zero_baumann_card
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Nat.card (ChapterB.baumann (T : Subgroup G)) = 4096 := by
  obtain ⟨f⟩ := source_a5_zero_original_baumann_dihedral_four_product D e hn hout hz
  rw [Nat.card_congr f.toEquiv]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card, DihedralGroup.card]

end CFSG.Quasithin.Chapter10
