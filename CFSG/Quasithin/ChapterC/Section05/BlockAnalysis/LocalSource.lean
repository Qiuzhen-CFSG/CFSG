module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.SourceEscape
/-!
# C.5.3 and C.5.5 with the original local SQTK hypothesis

The proper local subgroup H is SQTK in the simple ambient applications.
Restriction through RK≤H supplies the genuine earlier C.1.28 input; the
ambient group need not itself be SQTK. All original subgroup maps, the
block orbit, and the escaping conjugator remain unchanged.

Source: Aschbacher–Smith C.5.1–5, printed pp.154–155.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {H M K R T : Subgroup G}

theorem OriginalHypotheses.exists_moved_chiZero_of_local
    (d : OriginalHypotheses H M K R T) (outside : C128Outside 𝒦)
    (hH : IsSQTK 𝒦 H) (N : Subgroup H)
    (hN : (d.sylow : Subgroup H) ≤ N ∧ IsCoatom N) :
    ∃ L : Subgroup H, IsChiZeroBlockIn L ∧ ¬ L ≤ N ∧
      L = ⁅L,elementaryAbelianMaxJ (R.subgroupOf H)⁆ := by
  let J := R ⊔ K
  let B := (N.map H.subtype).subgroupOf J
  have hc := d.residual_characteristic_control N hN
  have hb := d.residual_maximal_restriction_ne_top N hN
  have hJ : IsSQTK 𝒦 J := (IsSQTK.equiv
    (subgroupOfEquivOfLe (sup_le d.R_le_H d.K_le_H))).mp (hH.subgroup (J.subgroupOf H))
  have hfJ := d.residual_join_fitting
  obtain ⟨L,hout,hL,hm⟩ := outside hJ hfJ d.residual_sylow B hc hb
  have hz : IsChiZeroBlockIn L := by
    rcases LocalC129.chi_zero_or_alternating_seven_in hJ.stronglyQuasithin hL with hz | ha
    · exact hz
    · exact False.elim (hout ((LocalC129.alternating_seven_le_control_of_c128_outside
        outside hJ hfJ d.residual_sylow hL.1 ha.2).trans hc))
  let f : J →* H := inclusion (sup_le d.R_le_H d.K_le_H)
  have hfi : Function.Injective f := inclusion_injective _
  have hfr : f.range.IsSubnormal := by
    rw [inclusion_range]
    exact d.residual_join_normal.isSubnormal
  have hP : (d.residual_sylow : Subgroup J).map f = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_map,map_subgroupOf_eq_of_le d.R_le_H]
    exact d.residual_sylow_image
  refine ⟨L.map f,chiZero_map f hfi hfr hz,?_,?_⟩
  · intro hLN
    apply hout
    intro l hl
    exact mem_map_of_mem H.subtype (hLN (mem_map_of_mem f hl))
  · have he := congrArg (Subgroup.map f) hm
    rw [map_commutator,←elementaryAbelianMaxJ_map_injective f hfi,hP] at he
    exact he


theorem OriginalHypotheses.block_decomposition_of_local
    (d : OriginalHypotheses H M K R T) (outside : C128Outside 𝒦) (hH : IsSQTK 𝒦 H) :
    Nonempty (OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H)
      (pResidual 2 H)) := by
  obtain ⟨N,hN,_⟩ := d.unique.2
  have hN' := And.intro hN.1 hN.2.isCoatom
  obtain ⟨L,hL,hout,hm⟩ := d.exists_moved_chiZero_of_local outside hH N hN'
  have hr : primeRank 3 H ≤ 2 := hH.stronglyQuasithin 3 Nat.prime_three (by decide)
  have hgen := block_orbit_eq_residual d.fitting hr d.sylow d.unique N hN' hL.chi hout
  apply orbitDecomposition_of_block d.fitting hr (d.sylow : Subgroup H)
    (R.subgroupOf H) (pResidual 2 H) ?_ hL hm hgen
  intro t ht
  have htR : (t : G) ∈ normalizer (R : Set G) :=
    d.R_normal (d.T_le (d.sylow_image ▸ mem_map_of_mem H.subtype ht))
  apply mem_normalizer_iff.mpr
  intro r
  exact mem_normalizer_iff.mp htR (r : G)


theorem OriginalHypotheses.blocks_and_noncommuting_conjugate_of_local
    (d : OriginalHypotheses H M K R T) {𝒦 : GroupClass.{u}}
    (outside : C128Outside 𝒦) (hH : IsSQTK 𝒦 H) :
    ∃ b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H),
      ∃ i₀ : Fin b.size, ∃ x ∈ M,
        ⁅moduleLayer ((b.block i₀).map H.subtype),
          (moduleLayer ((b.block i₀).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom⁆ ≠ ⊥ := by
  obtain ⟨b⟩ := d.block_decomposition_of_local outside hH
  let i₀ : Fin b.size := ⟨0,b.positive⟩
  obtain ⟨x,hx,hnc⟩ := d.exists_noncommuting_module b i₀
  rw [ambientModule_eq_literal] at hnc
  exact ⟨b,i₀,x,hx,hnc⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
