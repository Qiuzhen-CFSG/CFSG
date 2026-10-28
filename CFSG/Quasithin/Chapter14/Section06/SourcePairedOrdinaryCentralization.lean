module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding.PairCentralization
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedNormalizerBlocks
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedBorelAction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OrdinaryContainment
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import Theory.GroupTheory.Amalgam.LocalStructure
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115

/-!
# The original paired residual centralizes ordinary components of N(D)

Transport both original blocks to the literal residual-centralizer normalizer
with its unchanged full Sylow intersection. The source C.5 geometry gives
both full two-cores of order sixteen and an actual Sylow element exchanging
the commuting blocks. The marked-model exclusion then forces both blocks
to centralize every ordinary component; their join is the original residual.

Source: Aschbacher--Smith 14.6.9, printed p.1026, using 1.2.8(1--2).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open Chapter15.Section03.Candidates.ComponentStructure
universe v
variable {G : Type v} [Group G] [Finite G]

theorem source_paired_residual_centralizes_ordinary
    (T : Sylow 2 G) (I Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (S : Sylow 2 (normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)))
    (hS : (S : Subgroup _).map (normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)).subtype =
      (T : Subgroup G) ⊓ I) :
    let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)
    IsSQTK KnownSimple.IsKnownSimple ID →
    ∀ (A : Subgroup ID), IsComponent ID A →
      (∃ α : MulAut A, ModelAction115 A α) →
      (pResidual 2 I).map I.subtype ≤ centralizer (A.map ID.subtype : Set G) := by
  let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓
    centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)
  dsimp only
  intro hID A hA hm
  let B := (b.block i).map I.subtype
  let C := (b.block j).map I.subtype
  have hII : I ≤ ID := c.sylow_centralizer_normalized
  have hBI : B ≤ ID := (map_subtype_le _).trans hII
  have hCI : C ≤ ID := (map_subtype_le _).trans hII
  let eB := subgroupOfEquivOfLe hBI
  let eC := subgroupOfEquivOfLe hCI
  obtain ⟨⟨p⟩,⟨p'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  have hj : IsAlternatingBlock C 5 := p'.block
  have hBi := RankOne.Solvable.isAlternatingBlock_of_equiv eB.symm hi
  have hCi := RankOne.Solvable.isAlternatingBlock_of_equiv eC.symm hj
  obtain ⟨hbcore,hccore⟩ := source_paired_cores_eq_modules c b i j hij hs hi
  have hbcore' : pCore 2 B = blockU B := map_injective B.subtype_injective hbcore
  have hccore' : pCore 2 C = blockU C := map_injective C.subtype_injective hccore
  have hbcard : Nat.card (pCore 2 (B.subgroupOf ID)) = 16 := by
    rw [LocalCoreTransport.core_card 2 eB,hbcore',hi.blockU_card]
  have hccard : Nat.card (pCore 2 (C.subgroupOf ID)) = 16 := by
    rw [LocalCoreTransport.core_card 2 eC,hccore',hj.blockU_card]
  have hbc : ⁅B,C⁆ = ⊥ := by
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr (b.commute hij),Subgroup.map_bot]
  have hbci : ⁅B.subgroupOf ID,C.subgroupOf ID⁆ = ⊥ := by
    apply map_injective ID.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hBI,map_subgroupOf_eq_of_le hCI,hbc,Subgroup.map_bot]
  obtain ⟨t,ht,_,hswap⟩ := c.pair_exchange b i j hij
  let t' : ID := ⟨t,hII (c.R_le_H ht)⟩
  have hswap' : (B.subgroupOf ID).map (MulAut.conj t').toMonoidHom = C.subgroupOf ID := by
    apply map_injective ID.subtype_injective
    rw [map_subgroupOf_eq_of_le hCI,map_map]
    change (B.subgroupOf ID).map ((MulAut.conj t).toMonoidHom.comp ID.subtype) = C
    rw [←map_map,map_subgroupOf_eq_of_le hBI]
    exact hswap
  have hcentral := SourcePairedMovedEmbedding.local_conjugate_deleted_pair_centralizes_ordinary hID S (B.subgroupOf ID) (C.subgroupOf ID)
    (source_paired_block_local_in_centralizer_normalizer T I Λ c b i hi S hS)
    (source_paired_block_local_in_centralizer_normalizer T I Λ c b j hj S hS)
    hBi hCi hbcard hccard hbci ⟨t',hswap'⟩ A hA hm
  apply (c.pair_join b i j hij hs).symm.le.trans
  intro x hx a ha
  have hxID : x ∈ ID := (sup_le hBI hCI) hx
  have hxi : (⟨x,hxID⟩ : ID) ∈ B.subgroupOf ID ⊔ C.subgroupOf ID := by
    rw [←subgroupOf_sup hBI hCI]
    exact hx
  obtain ⟨a,ha,rfl⟩ := ha
  exact congrArg Subtype.val (hcentral hxi a ha)

end CFSG.Quasithin.Chapter14.Section06
