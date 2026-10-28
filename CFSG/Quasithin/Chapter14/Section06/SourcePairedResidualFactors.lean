module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointResidual
public import Theory.GroupTheory.CommutingCentralizerFactors
public import Theory.GroupTheory.PCoreCommutingProduct

/-!
# The point-centralizer product and its residual two-core

The marked source involution normalizes both disjoint C.5 blocks and
centralizes the original Sylow intersection R. Hence K intersect Mc is the
product of the two block point-centralizers, and I intersect Mc is its
product with R. Normality of K in I also shows that I intersect Mc
normalizes this joined point subgroup.

The source residual theorem identifies Kz = O²(I intersect Mc) with the
join of the two literal residuals Xi = O²(Ki intersect Mc). Disjointness
and commutation inherited from the blocks then identify O₂(Kz) with the
join of O₂(Xi). Thus the later equality Q1 = O₂(Kz) supplies exactly the
core product consumed by `source_paired_residual_core_exclusion`.
None of these steps needs D = 1.

Source: Aschbacher--Smith, proof of 14.6.9, printed pp.1026--1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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

include hG hempty hM hunique hmany hcard e hab H hH hu hI hij hs hi

/-- The literal paired point-centralizers split K intersect Mc and supplement R in I intersect Mc. -/
theorem source_paired_point_centralizer_product :
    let K₁ := (b.block i).map I.subtype
    let K₂ := (b.block j).map I.subtype
    let K := (pResidual 2 I).map I.subtype
    Disjoint K₁ K₂ ∧ K₁ ≤ centralizer (K₂ : Set G) ∧
      K ⊓ Mc = (K₁ ⊓ Mc) ⊔ (K₂ ⊓ Mc) ∧
      I ⊓ Mc = ((K₁ ⊓ Mc) ⊔ (K₂ ⊓ Mc)) ⊔ ((T : Subgroup G) ⊓ I) := by
  let R := (T : Subgroup G) ⊓ I
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let K := (pResidual 2 I).map I.subtype
  obtain ⟨z,hz,heq,hzS,hzR,hout,h,rest⟩ := source_paired_block_point_marking
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨_,⟨h'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₁ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hd : Disjoint K₁ K₂ := h.disjoint_blocks x (c.R_normal hx) hnc
  have hc : K₁ ≤ centralizer (K₂ : Set G) := le_centralizer_iff.mp h.commute
  have hK : K₁ ⊔ K₂ = K := c.pair_join b i j hij hs
  have hcentral : K ⊓ Mc = (K₁ ⊓ Mc) ⊔ (K₂ ⊓ Mc) := by
    rw [←hK,←heq]
    exact sup_inf_centralizer_singleton_of_disjoint_of_commuting K₁ K₂ z hd hc
      (h.normalizes hzS) (h'.normalizes hzS)
  have hRcentral : R ≤ centralizer ({z} : Set G) := by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (hzR r hr)
  have hgen : K ⊔ R = I := c.residual_sup_sylow
  have hprod : I ⊓ Mc = ((K₁ ⊓ Mc) ⊔ (K₂ ⊓ Mc)) ⊔ R := by
    rw [←hgen,←heq]
    rw [sup_inf_centralizer_singleton_of_centralizing_supplement K R z
      (c.R_le_H.trans c.normalizes_residual) hRcentral,heq,hcentral]
  exact ⟨hd,hc,hcentral,hprod⟩

/-- The actual point centralizer normalizes the join of its two block point-centralizers. -/
theorem source_paired_point_centralizer_normalizes :
    I ⊓ Mc ≤ normalizer ((((b.block i).map I.subtype ⊓ Mc) ⊔
      ((b.block j).map I.subtype ⊓ Mc) : Subgroup G) : Set G) := by
  have hC := (source_paired_point_centralizer_product
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi).2.2.1
  rw [←hC]
  exact (le_inf (inf_le_left.trans c.normalizes_residual)
    (inf_le_right.trans Mc.le_normalizer)).trans inf_normalizer_le_normalizer_inf

/-- The global residual two-core is the join of the cores of the literal block residuals. -/
theorem source_paired_residual_core_product :
    let K₁ := (b.block i).map I.subtype
    let K₂ := (b.block j).map I.subtype
    let B := I ⊓ Mc
    let Kz := (pResidual 2 B).map B.subtype
    let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
    let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
    Kz.pCoreIn 2 = X₁.pCoreIn 2 ⊔ X₂.pCoreIn 2 := by
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let B₁ := K₁ ⊓ Mc
  let B₂ := K₂ ⊓ Mc
  let Kz := (pResidual 2 (I ⊓ Mc : Subgroup G)).map (I ⊓ Mc).subtype
  let X₁ := (pResidual 2 B₁).map B₁.subtype
  let X₂ := (pResidual 2 B₂).map B₂.subtype
  obtain ⟨hd,hc,_,_⟩ := source_paired_point_centralizer_product
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hres : Kz = X₁ ⊔ X₂ := (source_paired_point_residuals
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi).1
  have hX₁ : X₁ ≤ K₁ := (map_subtype_le (pResidual 2 B₁)).trans inf_le_left
  have hX₂ : X₂ ≤ K₂ := (map_subtype_le (pResidual 2 B₂)).trans inf_le_left
  change Kz.pCoreIn 2 = X₁.pCoreIn 2 ⊔ X₂.pCoreIn 2
  rw [hres]
  exact pCoreIn_sup_of_disjoint_of_commuting 2 X₁ X₂ (hd.mono hX₁ hX₂)
    (hX₁.trans (hc.trans (centralizer_le hX₂)))

end CFSG.Quasithin.Chapter14.Section06
