module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.ShortModels
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer

/-!
# Typing the reconstructed seven-letter source block

Once C.1.21 has reconstructed shortness, its normal-layer argument identifies
U(L) with the actual full moved normal module. The original action therefore
has exactly O₂(L) as kernel on L. Its zero fixed subgroup identifies the
literal block quotient with that same module. Orders sixteen and sixty-four
give the exceptional and ordinary A₇ types; the six-dimensional recognition
supplies the actual permutation-module intertwiner.

These are applications of the constructed block, not quotient-to-block
implications. They preserve the original action map and its image marking.
Source: Aschbacher--Smith, C.1.24(a), printed pp.130--131; K.1.2, p.452.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

private theorem full_moved_layer (L U : Subgroup G) (hL : IsBlock L)
    [U.Normal] [IsElementaryAbelian 2 U] (hne : U ≠ ⊥) (hm : ⁅U,L⁆ = U) :
    (blockU L).map L.subtype = U := by
  exact (ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator
    L U hL (hm.symm ▸ hne)).trans hm

/-- Zero fixed points identify the block module cardinal with the original
full moved normal module. -/
theorem blockModule_card_of_full_moved (L U : Subgroup G) (hL : IsBlock L)
    [U.Normal] [IsElementaryAbelian 2 U] (hne : U ≠ ⊥) (hm : ⁅U,L⁆ = U)
    (hfix : U ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card (BlockModule L) = Nat.card U := by
  have he := full_moved_layer L U hL hne hm
  have hf : blockFixed L = ⊥ := by
    apply le_bot_iff.mp
    intro u hu
    have hc : ((u : L) : G) ∈ U ⊓ centralizer (L : Set G) := by
      refine ⟨he ▸ mem_map_of_mem L.subtype u.property, ?_⟩
      intro l hl
      exact congrArg L.subtype ((mem_center_iff.mp hu) ⟨l,hl⟩)
    rw [hfix] at hc
    exact Subtype.ext (Subtype.ext hc)
  rw [show Nat.card (BlockModule L) = Nat.card (blockU L) by
    rw [BlockModule, hf, Nat.card_congr (QuotientGroup.quotientBot (G := blockU L)).toEquiv]]
  exact (Nat.card_congr ((blockU L).equivMapOfInjective L.subtype L.subtype_injective).toEquiv).trans
    (Nat.card_congr (MulEquiv.subgroupCongr he).toEquiv)

/-- The original action induces the exact two-core quotient marking. -/
noncomputable def coreQuotientEquiv_of_full_moved (L U : Subgroup G) (hL : IsBlock L)
    [U.Normal] [IsElementaryAbelian 2 U] (hne : U ≠ ⊥) (hm : ⁅U,L⁆ = U)
    (q : G →* Q) (hk : q.ker = centralizer (U : Set G)) :
    (L ⧸ pCore 2 L) ≃* L.map q := by
  have he := full_moved_layer L U hL hne hm
  have hcore : (q.subgroupMap L).ker = pCore 2 L := by
    rw [← hL.short.centralizer_blockU]
    ext l
    constructor
    · intro hl u hu
      have hq : q (l : G) = 1 := congrArg Subtype.val hl
      have hc : (l : G) ∈ centralizer (U : Set G) := hk ▸ hq
      exact Subtype.ext (hc u (he ▸ mem_map_of_mem L.subtype hu))
    · intro hl
      have hc : (l : G) ∈ centralizer (U : Set G) := by
        intro u hu
        obtain ⟨a,ha,rfl⟩ := he.symm ▸ hu
        exact congrArg L.subtype (hl a ha)
      apply Subtype.ext
      change (l : G) ∈ q.ker
      exact hk.symm ▸ hc
  exact (QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective L))

/-- The original four-space action gives the exceptional block type. -/
theorem exceptional_block_of_full_four (L U : Subgroup G) (hL : IsBlock L)
    [U.Normal] [IsElementaryAbelian 2 U] (hm : ⁅U,L⁆ = U)
    (hfix : U ⊓ centralizer (L : Set G) = ⊥) (hcard : Nat.card U = 2 ^ 4)
    (q : G →* Q)
    (hk : q.ker = centralizer (U : Set G)) (e : L.map q ≃* alternatingGroup (Fin 7)) :
    IsExceptionalA7Block L := by
  have hne : U ≠ ⊥ := by intro hb; rw [hb, card_bot] at hcard; norm_num at hcard
  exact ⟨hL.short, ⟨(coreQuotientEquiv_of_full_moved L U hL hne hm q hk).trans e⟩,
    (blockModule_card_of_full_moved L U hL hne hm hfix).trans hcard⟩

/-- The original six-space action gives the ordinary block type and its
natural-module identification. -/
theorem ordinary_block_of_full_six (L U : Subgroup G) (hL : IsBlock L)
    [U.Normal] [IsElementaryAbelian 2 U] (hm : ⁅U,L⁆ = U)
    (hfix : U ⊓ centralizer (L : Set G) = ⊥) (hcard : Nat.card U = 2 ^ 6)
    (q : G →* Q)
    (hk : q.ker = centralizer (U : Set G)) (e : L.map q ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock L 7 := by
  have hne : U ≠ ⊥ := by intro hb; rw [hb, card_bot] at hcard; norm_num at hcard
  let := hL.short.elementary
  let := hL.short.module_elementary
  have hc : Nat.card (BlockModule L) = 2 ^ 6 :=
    (blockModule_card_of_full_moved L U hL hne hm hfix).trans hcard
  apply short_a7_block_of_six hL.short
    ((coreQuotientEquiv_of_full_moved L U hL hne hm q hk).trans e)
  have hd : 2 ^ Module.finrank (ZMod 2) (Additive (BlockModule L)) = 2 ^ 6 := by
    change Nat.card (Additive (BlockModule L)) = 2 ^ 6 at hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hd

end CFSG.Quasithin.ChapterC.RankOne.SevenSource
