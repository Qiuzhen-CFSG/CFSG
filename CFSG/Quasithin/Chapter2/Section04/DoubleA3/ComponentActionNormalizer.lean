module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionSource
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The original Sylow action normalizer bound

The component normalizer in the involution centralizer is normal and has
index at most two. Intersecting the prescribed Sylow subgroup with it gives
its actual Sylow subgroup. The original Thompson subgroup normalizes the
first cubic block and has relative index two, so its image bounds the index
of the normalizer of that block's automorphism image by two. No component
absorption or whole-Sylow normalization is assumed.

Source: Aschbacher–Smith, the inspection preceding 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- Canonical actor data before component absorption: the actual component
normalizer, its Sylow intersection, and its faithful first-block image. -/
theorem SourceCentralizerGeometry.component_action_normalizer_bound
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) :
    let H := involutionCentralizer g.z₂
    let N := normalizer (K : Set H)
    let L := (d.block.map d.H.subtype).subgroupOf H
    let B := (L.subgroupOf N).map K.normalizerMonoidHom
    ∃ P : Sylow 2 N, (P : Subgroup N) = (g.P₂ : Subgroup H).subgroupOf N ∧
      (normalizer (B : Set (MulAut K))).relIndex
        ((P : Subgroup N).map K.normalizerMonoidHom) ≤ 2 := by
  dsimp only
  let H := involutionCentralizer g.z₂
  let N := normalizer (K : Set H)
  let L := (d.block.map d.H.subtype).subgroupOf H
  let R := (sourceR d).subgroupOf H
  have hsq := hG.twoLocal_sqtk (isTwoLocal_involution_centralizer g.order_second)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  have hn : N.Normal := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hK.isCComponent with hk | hi
    · let := hk
      change (normalizer (K : Set H)).Normal
      rw [normalizer_eq_top]
      infer_instance
    · exact N.normal_of_index_eq_two hi
  let := hn
  obtain ⟨P,hP⟩ := g.P₂.exists_subgroupOf_eq_of_normal N
  have hLN : L ≤ N := g.first_block_normalizes_component hG K hK
  have hRL : R ≤ normalizer (L : Set H) := by
    intro r hr
    have hrB : (r:G) ∈ ChapterB.baumann ((d.S : Subgroup d.H).map d.H.subtype) := by
      rw [c.baumann]
      exact hr
    apply mem_normalizer_iff.mpr
    intro l
    exact mem_normalizer_iff.mp (c.first.normalizes hrB) l
  have hRN : R.subgroupOf N ≤ normalizer (L.subgroupOf N : Set N) := by
    rw [←subgroupOf_normalizer_eq hLN]
    exact comap_mono hRL
  have hRP : R.relIndex (g.P₂ : Subgroup H) = 2 := by
    have hh := relIndex_map_map_of_injective R (g.P₂ : Subgroup H) H.subtype_injective
    have hRH : sourceR d ≤ H := by
      intro r hr
      exact mem_centralizer_singleton_iff.mpr (g.second_fixed r hr)
    rw [show R.map H.subtype = sourceR d from map_subgroupOf_eq_of_le hRH] at hh
    exact hh.symm.trans g.second_index
  have hri : (R.subgroupOf N).relIndex (P : Subgroup N) ≤ 2 := by
    rw [hP]
    change (R.comap N.subtype).relIndex ((g.P₂ : Subgroup H).subgroupOf N) ≤ 2
    rw [relIndex_comap]
    exact (relIndex_le_of_le_right (show ((g.P₂ : Subgroup H).subgroupOf N).map N.subtype ≤ (g.P₂ : Subgroup H) from by
      rintro _ ⟨v,hv,rfl⟩
      exact hv) (by rw [hRP]; decide)).trans hRP.le
  refine ⟨P,hP,?_⟩
  rw [←relIndex_comap]
  apply le_trans (relIndex_le_of_le_left ?_ (show (R.subgroupOf N).relIndex (P : Subgroup N) ≠ 0 from index_ne_zero_of_finite)) hri
  intro r hr
  exact (L.subgroupOf N).le_normalizer_map K.normalizerMonoidHom
    (mem_map_of_mem K.normalizerMonoidHom (hRN hr))

end CFSG.Quasithin.Chapter2.DoubleA3
