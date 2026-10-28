module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.BlockOrbit

/-!
# C.5.3 from the original hypotheses

The original common-normal exclusion and unique maximal overgroup provide
the proper characteristic control needed by C.1.29. An actual moved χ₀
block outside that maximal subgroup then has transitive Sylow orbit
generating K = O²(H). The returned family has one or two distinct,
commuting blocks with the original J(R)-movement identity.

Only the independently owned universal C.1.28 source theorem remains
explicit. Source: Aschbacher–Smith C.5.3, printed pp.154–155.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {H M K R T : Subgroup G}

/-- C.5.3, with its actual subgroup orbit and the genuine earlier C.1.28
source input. No decomposition, block type, or conjugation data is assumed. -/
theorem OriginalHypotheses.block_decomposition
    (d : OriginalHypotheses H M K R T) (outside : C128Outside 𝒦) (hG : IsSQTK 𝒦 G) :
    Nonempty (OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H)
      (pResidual 2 H)) := by
  obtain ⟨N,hN,_⟩ := d.unique.2
  have hN' := And.intro hN.1 hN.2.isCoatom
  obtain ⟨L,hL,hout,hm⟩ := d.exists_moved_chiZero outside hG N hN'
  have hr : primeRank 3 H ≤ 2 := (hG.subgroup H).stronglyQuasithin 3 Nat.prime_three (by decide)
  have hgen := block_orbit_eq_residual d.fitting hr d.sylow d.unique N hN' hL.chi hout
  apply orbitDecomposition_of_block d.fitting hr (d.sylow : Subgroup H)
    (R.subgroupOf H) (pResidual 2 H) ?_ hL hm hgen
  intro t ht
  have htR : (t : G) ∈ normalizer (R : Set G) :=
    d.R_normal (d.T_le (d.sylow_image ▸ mem_map_of_mem H.subtype ht))
  apply mem_normalizer_iff.mpr
  intro r
  exact mem_normalizer_iff.mp htR (r : G)

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
