module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedCoreContradiction
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCentralizer
public import Theory.GroupTheory.OmegaCenterProductOrders

/-!
# The paired-source contradiction from its literal residual-core product

Let Rᵢ be the two-core of the two-residual of Kᵢ ∩ Mc for the actual
paired C.5 blocks. Their point-centralizer models give center order two.
The noncommuting conjugate separates the whole blocks, and the block orbit
supplies an element of T interchanging them. Since T lies in Mc, this
same element interchanges R₁ and R₂. Thus the single equality
O₂(Mc) = R₁ ∨ R₂ supplies every input of the final plane-normalizer
contradiction. Proving that equality remains with the paired centralizer
and irreducible-section argument; it is not a consequence of the model
orders alone.

Source: Aschbacher--Smith, proof of 14.6.9(i)--(n), printed p.1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_paired_residual_core_exclusion
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
    (hQ : Mc.pCoreIn 2 =
      (((pResidual 2 ((b.block i).map I.subtype ⊓ Mc : Subgroup G)).map
        ((b.block i).map I.subtype ⊓ Mc).subtype).pCoreIn 2) ⊔
      (((pResidual 2 ((b.block j).map I.subtype ⊓ Mc : Subgroup G)).map
        ((b.block j).map I.subtype ⊓ Mc).subtype).pCoreIn 2))
 : False := by
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let B₁ := K₁ ⊓ Mc
  let B₂ := K₂ ⊓ Mc
  let X₁ := (pResidual 2 B₁).map B₁.subtype
  let X₂ := (pResidual 2 B₂).map B₂.subtype
  let R₁ := X₁.pCoreIn 2
  let R₂ := X₂.pCoreIn 2
  obtain ⟨⟨h⟩,⟨h'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  have hc₁ := (source_paired_block_borel_core hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi).2.2
  have hc₂ := (source_paired_block_borel_core hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b j i (Ne.symm hij) hs h'.block).2.2
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₁ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hdK : Disjoint K₁ K₂ := h.disjoint_blocks x (c.R_normal hx) hnc
  have hR₁ : R₁ ≤ K₁ := (pCoreIn_le 2 X₁).trans
    ((map_subtype_le (pResidual 2 B₁)).trans inf_le_left)
  have hR₂ : R₂ ≤ K₂ := (pCoreIn_le 2 X₂).trans
    ((map_subtype_le (pResidual 2 B₂)).trans inf_le_left)
  have hd : Disjoint R₁ R₂ := hdK.mono hR₁ hR₂
  have hc : R₁ ≤ centralizer (R₂ : Set G) :=
    hR₁.trans ((le_centralizer_iff.mp h.commute).trans (centralizer_le hR₂))
  obtain ⟨s,hsS,hblocks⟩ := b.transitive i j
  let t : G := (s : G)⁻¹
  have hsR : (s : G) ∈ (T : Subgroup G) ⊓ I := by
    rw [←c.sylow_image]
    exact mem_map_of_mem I.subtype hsS
  have ht : t ∈ (T : Subgroup G) := (T : Subgroup G).inv_mem hsR.1
  have hblocks' : K₁.map (MulAut.conj t).toMonoidHom = K₂ := by
    change ((b.block i).map I.subtype).map (MulAut.conj t).toMonoidHom =
      (b.block j).map I.subtype
    rw [hblocks,map_map,map_map]
    rfl
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hMc := (plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ).2.2.1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hMcmap : Mc.map (MulAut.conj t).toMonoidHom = Mc :=
    mem_normalizer_iff_map_conj_eq.mp (Mc.le_normalizer (hTMc ht))
  have hBmap : B₁.map (MulAut.conj t).toMonoidHom = B₂ := by
    change (K₁ ⊓ Mc).map (MulAut.conj t).toMonoidHom = K₂ ⊓ Mc
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective,hblocks',hMcmap]
  have hswap : R₁.map (MulAut.conj t).toMonoidHom = R₂ := by
    change (X₁.pCoreIn 2).map (MulAut.conj t).toMonoidHom = X₂.pCoreIn 2
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj t).injective]
    congr 1
    change ((pResidual 2 B₁).map B₁.subtype).map (MulAut.conj t).toMonoidHom = _
    rw [map_embedded_pResidual,hBmap]
  apply source_paired_core_exclusion hG T hempty hM hunique hmany hcard e hab
    R₁ R₂ t hQ hd hc ht hswap
  rw [hQ]
  exact omegaOneCenterAmbient_card_four_of_disjoint_of_center_card_two R₁ R₂ hd hc hc₁ hc₂

end CFSG.Quasithin.Chapter14.Section06
