module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCentralizer
public import Theory.GroupTheory.PairedNormalPSubgroup
public import Theory.GroupTheory.SylowLocalCore

/-!
# The point-centralizer two-core preserves both original blocks

Each original point-centralizer block contains a cubic element, supplied by
its actual binary A₄ model. A normal two-subgroup of I ∩ Mc inside T ∩ I
cannot exchange the commuting disjoint blocks: the independent cubic
commutator would be both a two-element and a three-element.
This removes the factor exchange from the action on the literal point core.

Source: Aschbacher--Smith, 14.6.9(l), printed p.1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal source action fixes a block whenever the acting two-group
is normalized by I ∩ Mc. This applies in particular to O₂(I ∩ Mc). -/
theorem source_paired_normal_twoGroup_normalizes_block
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (W : Subgroup G) (hW : IsPGroup 2 W)
    (hWR : W ≤ (T : Subgroup G) ⊓ I)
    (hBW : I ⊓ Mc ≤ normalizer (W : Set G)) :
    W ≤ normalizer (((b.block i).map I.subtype : Subgroup G) : Set G) := by
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  obtain ⟨⟨h⟩,_⟩ := c.alternating_paired_setups b i j hij hs hi
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₁ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hd : Disjoint K₁ K₂ := h.disjoint_blocks x (c.R_normal hx) hnc
  obtain ⟨eb⟩ := source_paired_block_borel hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi
  have hb : Nat.card BinaryPermutation.AlternatingFiveBorel.B = 12 :=
    (Nat.card_congr BinaryPermutation.AlternatingFiveBorel.marking.toEquiv.symm).trans
      (alternatingGroup.card_of_card_eq_four (by simp))
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card'
    (G := BinaryPermutation.AlternatingFiveBorel.B) 3 (by rw [hb]; decide)
  let aB : ↥(K₁ ⊓ Mc) := eb.symm (SemidirectProduct.inr a)
  have haB : orderOf aB = 3 := by
    rw [eb.symm.orderOf_eq]
    exact (orderOf_injective _ SemidirectProduct.inr_injective a).trans ha
  have haG : orderOf (aB : G) = 3 := (orderOf_coe aB).trans haB
  have ha3 : (aB : G)^3 = 1 := haG ▸ pow_orderOf_eq_one (aB : G)
  have hane : (aB : G) ≠ 1 := by
    intro he
    simp only [he,orderOf_one] at haG
    contradiction
  have haW : (aB : G) ∈ normalizer (W : Set G) :=
    hBW ⟨map_subtype_le _ aB.property.1,aB.property.2⟩
  intro w hw
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (c.pair_action b i j hij hs w (hWR hw)).resolve_right
    (twoGroup_cannot_exchange_disjoint_of_cubic K₁ K₂ W hW hd
      (le_centralizer_iff.mp h.commute) aB aB.property.1 haW ha3 hane w hw)

/-- The actual two-core of I ∩ Mc preserves each original factor. -/
theorem source_paired_point_core_normalizes_blocks
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    (I ⊓ Mc).pCoreIn 2 ≤
      normalizer (((b.block i).map I.subtype : Subgroup G) : Set G) ⊓
      normalizer (((b.block j).map I.subtype : Subgroup G) : Set G) := by
  let R := (T : Subgroup G) ⊓ I
  let B := I ⊓ Mc
  let W := B.pCoreIn 2
  obtain ⟨z,_,heq,_,hzR,_,_,_,_,_,_⟩ :=
    source_paired_block_point_marking hG T hempty hM hunique hmany hcard e hab
      H hH u hu I hI Λ c b i j hij hs hi
  have hRB : R ≤ B := by
    intro r hr
    refine ⟨hr.2,?_⟩
    rw [←heq]
    exact mem_centralizer_singleton_iff.mpr (hzR r hr)
  obtain ⟨PB,hPB⟩ := c.sylow.exists_map_subtype_eq_of_le
    (show B ≤ I from inf_le_left) (by rw [c.sylow_image]; exact hRB)
  have hWR : W ≤ R := (pCoreIn_le_sylow B PB).trans_eq (hPB.trans c.sylow_image)
  have hW : IsPGroup 2 W := isPGroup_pCoreIn 2 B
  have hBW : B ≤ normalizer (W : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  obtain ⟨_,⟨h'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  exact le_inf
    (source_paired_normal_twoGroup_normalizes_block hG T hempty hM hunique hmany hcard
      e hab H hH u hu I hI Λ c b i j hij hs hi W hW hWR hBW)
    (source_paired_normal_twoGroup_normalizes_block hG T hempty hM hunique hmany hcard
      e hab H hH u hu I hI Λ c b j i hij.symm hs h'.block W hW hWR hBW)

end CFSG.Quasithin.Chapter14.Section06
