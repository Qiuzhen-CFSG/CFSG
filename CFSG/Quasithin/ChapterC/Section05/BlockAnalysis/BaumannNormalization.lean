module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.BaumannNormalization.Family
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.BlockSylow

/-!
# C.5.4(1) for the original block family

The original C.5.3 orbit supplies literal permutation, movement and
commuting distinct factors. Its original Sylow intersection and module
placement discharge every hypothesis of the chi-zero normalization
theorem. Mapping along H→G retains the original R and each actual block.
The final producer constructs the family from C.5.1--2 and the genuine
earlier C.1.28 source; no normalization conclusion is assumed.

Source: Aschbacher--Smith C.5.3--4, printed pp.154--155, via C.1.16(2),
printed pp.125--126 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {H M K R T : Subgroup G}

/-- C.5.4(1) for the original C.5.3 family: the actual Baumann subgroup
normalizes every actual embedded block. -/
theorem OriginalHypotheses.baumann_normalizes_block
    (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i : Fin b.size) :
    ChapterB.baumann R ≤ normalizer ((b.block i).map H.subtype : Set G) := by
  let L : Fin b.size → Subgroup G := fun j => (b.block j).map H.subtype
  have hperm : ∀ g ∈ R, ∀ j, ∃ k, (L j).map (MulAut.conj g).toMonoidHom = L k := by
    intro g hg j
    let s : H := ⟨g,d.R_le_H hg⟩
    have hs : s ∈ (d.sylow : Subgroup H) := by
      obtain ⟨t,ht,he⟩ := d.sylow_image.symm ▸ d.R_le hg
      exact (Subtype.ext he : t=s) ▸ ht
    obtain ⟨k,hk⟩ := b.permutes s hs j
    refine ⟨k,?_⟩
    change ((b.block j).map H.subtype).map (MulAut.conj g).toMonoidHom = (b.block k).map H.subtype
    rw [hk,map_map,map_map]
    rfl
  have hc : Pairwise fun j k => ⁅L j,L k⁆ = ⊥ := by
    intro j k hjk
    change ⁅(b.block j).map H.subtype,(b.block k).map H.subtype⁆ = ⊥
    rw [←map_commutator, commutator_eq_bot_iff_le_centralizer.mpr (b.commute hjk),Subgroup.map_bot]
  have hm : L i = ⁅L i,elementaryAbelianMaxJ R⁆ := by
    have he := congrArg (map H.subtype) (b.moved i)
    rw [map_commutator, ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le d.R_le_H] at he
    exact he
  have ht : IsChiZeroBlock (L i) :=
    chiZero_equiv (equivMapOfInjective (b.block i) H.subtype H.subtype_injective) (b.type i).2
  obtain ⟨P,hP⟩ := d.block_sylow b i
  have hu : (blockU (L i)).map (L i).subtype ≤ R := by
    have hh := d.module_le_R b i
    rwa [ambientModule_eq_literal] at hh
  exact RankOne.ChiProduct.BaumannNormalization.normalizes_chiZero R L hperm hc i
    d.R_twoGroup hu hm ht P hP

/-- Original C.5.1--2 and the earlier C.1.28 source construct a block family
satisfying C.5.3 and C.5.4(1), without a block-normalization assumption. -/
theorem OriginalHypotheses.exists_baumann_normalized_blocks
    (d : OriginalHypotheses H M K R T) {𝒦 : GroupClass}
    (outside : C128Outside 𝒦) (hG : IsSQTK 𝒦 G) :
    ∃ b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H),
      ∀ i, ChapterB.baumann R ≤ normalizer ((b.block i).map H.subtype : Set G) := by
  obtain ⟨b⟩ := d.block_decomposition outside hG
  exact ⟨b,d.baumann_normalizes_block b⟩
end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
