module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.ResidualCentralizer
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.LocalMaximality

/-!
# Maximality of the original paired blocks in the D-normalizer

A local C-component for the full Sylow cannot be properly contained in a
chi-zero block. The cubic row is solvable. In either noncubic row the block
has a characteristic-two rank-one quotient, whose proper Sylow overgroups
are solvable; the existing rank-one cover theorem therefore gives equality.

The source adapters place each original paired A5 block in the local
C-component family of the literal normalizer of D, with the same full
Sylow intersection. They discharge the maximality step in14.6.9 once the
containing C.1.29 block is selected. Selection of that containing block is
separate from maximality; no subnormality in the larger normalizer is
assumed here.

Source: Aschbacher--Smith14.6.9, printed p.1026, using C.1.29 and A.3.12.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

private theorem alternating_five_quotient_quasisimple {A : Type*} [Group A]
    (ha : IsAlternatingBlock A 5) : IsQuasisimple (A ⧸ pCore 2 A) := by
  rcases ha.2.1.quotient with hq | hc
  · exact hq
  · obtain ⟨e⟩ := ha.2.2.quotient_iso
    have he : Nat.card (A ⧸ pCore 2 A) = 60 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num
    omega

/-- Each original A5 block is a local C-component for the actual full
Sylow of N_G(D). This does not assume it is subnormal in N_G(D). -/
theorem source_paired_block_local_in_centralizer_normalizer
    (T : Sylow 2 G) (I Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i : Fin b.size) (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (S : Sylow 2 (normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)))
    (hS : (S : Subgroup _).map (normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)).subtype =
      (T : Subgroup G) ⊓ I) :
    let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)
    ((b.block i).map I.subtype).subgroupOf ID ∈ ChapterA.Section03.localCComponents S := by
  let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓
    centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)
  have hID : I ≤ ID := c.sylow_centralizer_normalized
  let f := inclusion hID
  have hf : Function.Injective f := inclusion_injective hID
  have hk : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff f).mpr hf
  let : Group.IsSolvable f.ker := hk ▸ inferInstanceAs (Group.IsSolvable (⊥ : Subgroup I))
  let e := (b.block i).equivMapOfInjective I.subtype I.subtype_injective
  have ha := RankOne.Solvable.isAlternatingBlock_of_equiv e.symm hi
  let : IsQuasisimple ((b.block i) ⧸ pCore 2 (b.block i)) :=
    alternating_five_quotient_quasisimple ha
  have hc : (b.block i).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (b.type i).1.subnormal ha.2.1.twoPerfect
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker
    (ChapterA.Section03.isCComponent_mem_localCComponents
      (T := (c.sylow : Subgroup I)) hc) f
  have hs : (c.sylow : Subgroup I).map f = (S : Subgroup ID) := by
    apply map_injective ID.subtype_injective
    rw [map_map,hS]
    exact c.sylow_image
  have hb : (b.block i).map f = ((b.block i).map I.subtype).subgroupOf ID := by
    apply map_injective ID.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le ((map_subtype_le _).trans hID)]
    rfl
  rwa [hs,hb] at hl

/-- Literal14.6.9 maximality consumer: any selected C.1.29 block containing
an original paired block is exactly that original block in N_G(D). -/
theorem source_paired_block_eq_containing_chiZero
    (T : Sylow 2 G) (I Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i : Fin b.size) (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (S : Sylow 2 (normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)))
    (hS : (S : Subgroup _).map (normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)).subtype =
      (T : Subgroup G) ⊓ I)
    (L : Subgroup (normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)))
    (hL : IsChiZeroBlockIn L)
    (hle : ((b.block i).map I.subtype).subgroupOf _ ≤ L) :
    ((b.block i).map I.subtype).subgroupOf _ = L :=
  local_component_eq_chiZero_of_le S
    (source_paired_block_local_in_centralizer_normalizer T I Λ c b i hi S hS) hL hle

private theorem source_paired_chi_pair_of_containing_chiZero
    (T : Sylow 2 G) (I Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    let K := (pResidual 2 I).map I.subtype
    let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓ centralizer (K : Set G) : Set G)
    ∀ (S : Sylow 2 ID), (S : Subgroup ID).map ID.subtype = (T : Subgroup G) ⊓ I →
      ∀ L : Subgroup ID, IsChiZeroBlockIn L →
        ((b.block i).map I.subtype).subgroupOf ID ≤ L →
        IsChiBlockIn (((b.block i).map I.subtype).subgroupOf ID) ∧
        IsChiBlockIn (((b.block j).map I.subtype).subgroupOf ID) ∧
        ((b.block i).map I.subtype).subgroupOf ID ≠ ((b.block j).map I.subtype).subgroupOf ID ∧
        ((b.block i).map I.subtype).subgroupOf ID ⊔
          ((b.block j).map I.subtype).subgroupOf ID = K.subgroupOf ID := by
  intro K ID S hS L hL hle
  have hID : I ≤ ID := c.sylow_centralizer_normalized
  let A := ((b.block i).map I.subtype).subgroupOf ID
  let B := ((b.block j).map I.subtype).subgroupOf ID
  have hiID : (b.block i).map I.subtype ≤ ID := (map_subtype_le _).trans hID
  have hjID : (b.block j).map I.subtype ≤ ID := (map_subtype_le _).trans hID
  have he : A = L := source_paired_block_eq_containing_chiZero T I Λ c b i hi S hS L hL hle
  have hA : IsChiBlockIn A := he.symm ▸ ⟨hL.1,hL.2.chi⟩
  obtain ⟨t,ht,_,htij⟩ := c.pair_exchange b i j hij
  let tD : ID := ⟨t,hID ht.2⟩
  have hAB : A.map (MulAut.conj tD).toMonoidHom = B := by
    apply map_injective ID.subtype_injective
    rw [map_subgroupOf_eq_of_le hjID,map_map]
    have hh : ID.subtype.comp (MulAut.conj tD).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp ID.subtype := rfl
    rw [hh,←map_map,map_subgroupOf_eq_of_le hiID]
    exact htij
  have hB : IsChiBlockIn B := hAB ▸ RankOne.ChiProduct.chi_map_equiv (MulAut.conj tD) hA
  have hne : A ≠ B := by
    intro heq
    have hh := congrArg (map ID.subtype) heq
    rw [map_subgroupOf_eq_of_le hiID,map_subgroupOf_eq_of_le hjID] at hh
    exact hij (b.injective (map_injective I.subtype_injective hh))
  have hjoin : A ⊔ B = K.subgroupOf ID := by
    change (((b.block i).map I.subtype).subgroupOf ID) ⊔
      (((b.block j).map I.subtype).subgroupOf ID) = K.subgroupOf ID
    rw [←subgroupOf_sup hiID hjID,c.pair_join b i j hij hs]
  exact ⟨hA,hB,hne,hjoin⟩

/-- One containing ambient chi-zero block suffices for normality of the original
pair, using its actual Sylow exchanger and the ambient three-rank bound. -/
theorem source_paired_residual_normal_of_containing_chiZero
    (T : Sylow 2 G) (I Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    let K := (pResidual 2 I).map I.subtype
    let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓ centralizer (K : Set G) : Set G)
    ∀ (S : Sylow 2 ID), (S : Subgroup ID).map ID.subtype = (T : Subgroup G) ⊓ I →
      generalizedFitting ID = pCore 2 ID → primeRank 3 ID ≤ 2 →
      ∀ L : Subgroup ID, IsChiZeroBlockIn L →
        ((b.block i).map I.subtype).subgroupOf ID ≤ L → ID ≤ normalizer (K : Set G) := by
  intro K ID S hS hf hr L hL hle
  obtain ⟨hA,hB,hne,hjoin⟩ :=
    source_paired_chi_pair_of_containing_chiZero T I Λ c b i j hij hs hi S hS L hL hle
  have hn : (K.subgroupOf ID).Normal := hjoin ▸ chi_pair_join_normal hf hr hA hB hne
  exact (normal_subgroupOf_iff_le_normalizer
    ((map_subtype_le _).trans c.sylow_centralizer_normalized)).mp hn

/-- The same single containing-block witness gives the literal ordered product
N(D) = K (N(D) ∩ Mc) under the original characteristic-normalizer control. -/
theorem source_paired_normalizer_product_of_containing_chiZero
    (T : Sylow 2 G) (I Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    let K := (pResidual 2 I).map I.subtype
    let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓ centralizer (K : Set G) : Set G)
    ∀ (S : Sylow 2 ID), (S : Subgroup ID).map ID.subtype = (T : Subgroup G) ⊓ I →
      generalizedFitting ID = pCore 2 ID → IsSQTK KnownSimple.IsKnownSimple ID →
      ∀ Mc : Subgroup G, (S : Subgroup ID).characteristicNormalizerClosure ≤ Mc.subgroupOf ID →
      ∀ L : Subgroup ID, IsChiZeroBlockIn L →
        ((b.block i).map I.subtype).subgroupOf ID ≤ L →
        ∀ g : ID, ∃ k : K.subgroupOf ID, ∃ m : Mc.subgroupOf ID,
          g = (k : ID) * (m : ID) := by
  intro K ID S hS hf hsqtk Mc hcpu L hL hle
  obtain ⟨hA,hB,hne,hjoin⟩ :=
    source_paired_chi_pair_of_containing_chiZero T I Λ c b i j hij hs hi S hS L hL hle
  have hp := (chi_pair_product_knownSimple hsqtk hf S (Mc.subgroupOf ID) hcpu hA hB hne).2
  rwa [hjoin] at hp

end CFSG.Quasithin.Chapter14.Section06
