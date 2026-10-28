module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryMovingBlocks
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingStarSixExclusion
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarSylow
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneBlocks
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.BlockKernel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.QuotientCardSixty
public import Theory.SpecificGroups.AlternatingFiveSylowRadical

/-!
# The five-letter constrained component on the original paired plane

A full component Sylow normalizing the original Q descends to its literal
star quotient. In an A₅ star extension the normalized radical contains that
Sylow. Lifting through the full star kernel makes Q Sylow in KQ. C.2.5 then
reduces K to a natural L₂(4) block or the deleted A₅ block; the actual core
quotient determines the field degree. The central star kernel is retained
until the block action proves its restriction to K is exactly O₂(K).

The chosen-module application NonFFSourceDoubledBinaryFiveStar supplies the
original Sylow and excludes the deleted block by its Sylow-fixed line.
The natural L₂(4) case, the remaining constrained rows and final non-FF
assembly remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, 7.7.9(1), printed p.708, C.2.5 and C.2.7,
printed pp.144–147, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFiveStar
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {H K Q M : Subgroup G}

theorem five_star_core_sylow
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ normalizer (Q : Set G))
    (e : starImage K Q K ≃* alternatingGroup (Fin 5)) :
    Chapter1.IsSylowIn 2 Q (K ⊔ Q) := by
  let J := K ⊔ Q
  let C := starImage K Q K
  let q := QuotientGroup.mk' (starKernel K Q)
  let : (K.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let Pstar := P.mapSurjective (toStarImage_surjective K Q)
  obtain ⟨f,hf,hmark⟩ := alternating_star_embedding h (by decide) (by decide) e
  have hn : (Pstar : Subgroup C).map C.subtype ≤
      normalizer (starImage K Q Q : Set (StarQuotient K Q)) := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    apply (Q.subgroupOf J).le_normalizer_map q
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq (show Q ≤ J from le_sup_right)]
    exact hPQ (mem_map_of_mem K.subtype hy)
  have hs := alternatingGroup.sylow_le_intersection_of_normalized_radical_five
    C (starImage K Q Q) e f hf hmark Pstar
    (star_radical_ne_bot (source_join_input h)) hn
    (star_intersection_normalizer_core_from_source h)
  obtain ⟨S,hS⟩ := radical_sylow_of_star_component_sylow (source_join_input h)
    Pstar (map_le_iff_le_comap.mpr hs)
  exact ⟨S,by rw [hS,map_subgroupOf_eq_of_le le_sup_right]⟩

private theorem five_star_eq_core_of_block
    (h : Input KnownSimple.IsKnownSimple H Q M K) (hs : ChapterC.IsShort K) :
    Nonempty ((K ⧸ pCore 2 K) ≃* starImage K Q K) := by
  have hb : ChapterC.IsBlock (K.subgroupOf (K ⊔ Q)) :=
    ⟨inferInstance,hs.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm,
      (h.component.2.subgroupOf_of_le le_sup_left h.join_le).subnormal⟩
  exact ⟨MulEquiv.ofBijective (coreToStar h.normalizes)
    ⟨coreToStar_injective_of_block h.normalizes hb,coreToStar_surjective h.normalizes⟩⟩

theorem five_star_natural_or_deleted
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ normalizer (Q : Set G))
    (e : starImage K Q K ≃* alternatingGroup (Fin 5)) :
    Chapter1.IsSylowIn 2 Q (K ⊔ Q) ∧
      (ChapterC.IsL2EvenBlock K 2 ∨ ChapterC.IsAlternatingBlock K 5) := by
  have hSyl := five_star_core_sylow h P hPQ e
  refine ⟨hSyl,?_⟩
  rcases source_rankOne_blocks_of_sylow h hSyl with ⟨n,hn⟩ | h5
  · obtain ⟨a⟩ := five_star_eq_core_of_block h hn.2.1
    have hc : Nat.card (K ⧸ pCore 2 K) = 60 := by
      rw [Nat.card_congr (a.trans e).toEquiv,nat_card_alternatingGroup]
      norm_num
    exact Or.inl (hn.four_of_quotient_card hc)
  · exact Or.inr h5

theorem deleted_five_core_sylow
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ normalizer (Q : Set G))
    (hb : ChapterC.IsAlternatingBlock K 5) : Chapter1.IsSylowIn 2 Q (K ⊔ Q) := by
  obtain ⟨a⟩ := five_star_eq_core_of_block h hb.2.1
  obtain ⟨b⟩ := hb.2.2.quotient_iso
  exact five_star_core_sylow h P hPQ (a.symm.trans b)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFiveStar
