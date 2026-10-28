module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.CubicPairSource
public import CFSG.Quasithin.ChapterC.Section06.Thompson.CubicPairOriginal
/-!
# Thompson stability and the family kernel for the selected cubic pair

The original Chapter 2 decomposition supplies both actual cubic blocks,
their exchanging element and the escaping conjugate. Its core-centralizer
identity discharges the last local input to C.6.1 Thompson stability.
The 2.4.4 normalizer control then identifies the full Sylow action kernel
on the four maximum elementary subgroups with the original Thompson subgroup.

Source: Aschbacher–Smith 2.4.4–5, C.6.1 case (beta), printed pp.527–528,165.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.cubic_pair_thompson_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hpairwise : d.L0 ≠ d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3)
    (M₀ : Subgroup G) (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    elementaryAbelianMaxJ M₀ = elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  obtain ⟨L,c,F,F',hF,hF',h,h',hL,hKL,hjoin,hpair,ht,x,hx,hnc⟩ :=
    d.cubic_pair_configuration hG T hST hpairwise hK M₀ hSM hMT hi
  have ht' : ∃ t ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy t = L := by
    obtain ⟨t,ht,he⟩ := ht
    exact ⟨t,ht,he⟩
  have hcl := d.two_block_closures L hpair ht'
  have hfull := d.two_block_core_centralizer L h.short h'.short hKL hpair ht'
  rw [hcl.2] at hfull
  exact ChapterC.Section06.cubic_pair_thompson_stable_from_original c h h' hK hL
    hKL hpair ht hfull hi x hx hnc

theorem MinimalBlockSetup.cubic_pair_family_action
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpairwise : d.L0 ≠ d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    (elementaryAbelianMaxJ R).relIndex R = 2 ∧
      ∀ g ∈ (T : Subgroup G),
        (∀ A ∈ elementaryAbelianMaxSubgroups R, g ∈ normalizer (A : Set G)) ↔
          g ∈ elementaryAbelianMaxJ R := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨L,c,F,F',hF,hF',h,h',hL,hKL,hjoin,hpair,ht,x,hx,hnc⟩ :=
    d.cubic_pair_configuration hG T hST.le hpairwise hK M₀ hSM hMT hi
  have ht' : ∃ t ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy t = L := by
    obtain ⟨t,ht,he⟩ := ht
    exact ⟨t,ht,he⟩
  have hcl := d.two_block_closures L hpair ht'
  have hfull := d.two_block_core_centralizer L h.short h'.short hKL hpair ht'
  rw [hcl.2] at hfull
  have hQ : twoCore d.H ≠ ⊥ := by
    intro he
    have hU : sourceModule (d.block.map d.H.subtype) ≤ twoCore d.H := by
      let := h.elementary
      have hUC : sourceModule (d.block.map d.H.subtype) ≤
          centralizer (sourceModule (d.block.map d.H.subtype) ⊔ sourceModule L : Subgroup G) :=
        le_centralizer_iff.mpr (sup_le (le_centralizer (RankOne.U (d.block.map d.H.subtype)))
          ((map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _)))))
      exact (le_inf (h.module_le.trans inf_le_left) hUC).trans hfull.le
    exact moduleLayer_ne_bot hK.2.1 (bot_unique (he ▸ hU))
  have hQR : twoCore d.H ≤ (d.S : Subgroup d.H).map d.H.subtype := pCoreIn_le_sylow d.H d.S
  have hnormal : (twoCore d.H).subgroupOf d.H |>.Normal :=
    (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 d.H)).mpr
      (d.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.H (pCore 2 d.H)))
  have hc := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
    (twoCore d.H) hQ hQR hnormal
  exact ChapterC.Section06.cubic_pair_family_kernel_from_original c h h' hK hL
    hKL hpair ht hfull T hc hi x hx hnc
end CFSG.Quasithin.Chapter2
