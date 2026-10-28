module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PlacedModelReduction
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.OddComponents
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentNormalityComplete
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PairSylow

/-!
# Complete inspection once the original residual is placed

The binary local exclusions and finite rank exclusions leave the odd
Theorem B models, whose two-rank is at most seven. The actual residual
placement forces two-rank at least eight. Thus no selected component can
contain the residual. Normality and covering uniqueness turn any proved
inner action into precisely that placement, so a small Sylow Frattini
quotient suffices for the original component contradiction.

Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The complete model inspection excludes a selected component containing
the literal original residual. No outer or model premise is added. -/
theorem source_a5_oddNormalizer_no_placed_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) : False := by
  exact source_a5_oddNormalizer_component_no_odd_model
    D e hn hp B hB hBC hBV hperm K hK houtK hFK
      (source_a5_oddNormalizer_placed_component_odd_model
        D e hn hp B hB hBC hBV hperm K hK houtK hFK
          (source_oddNormalizer_component_theoremB D B hne K hK))

/-- Proved inner action suffices for the full original component exclusion.
The actual normality theorem supplies overlap normalization for closure. -/
theorem source_a5_oddNormalizer_no_inner_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hi : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    False := by
  let : K.Normal := source_a5_oddNormalizer_component_normal
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  have hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))) := by
    intro y _
    exact le_normalizer_of_normal (mem_top y)
  obtain ⟨_, _, _, hF⟩ := source_a5_oddNormalizer_component_closure_of_overlap_normalizes
    D e hn hp B hB hBC hBV hperm K hK houtK hYK hi
  exact source_a5_oddNormalizer_no_placed_component
    D e hn hp B hne hB hBC hBV hperm K hK houtK hF

/-- Any actual model bound on a Sylow Frattini quotient of the selected
component now feeds the complete source contradiction directly. -/
theorem source_a5_oddNormalizer_no_smallFrattini_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (P : Sylow 2 (K ⧸ center K))
    (hP : Nat.card (P ⧸ frattini P) ≤ 128) : False := by
  let : K.Normal := source_a5_oddNormalizer_component_normal
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  let : IsQuasisimple K := hK.2
  exact source_a5_oddNormalizer_no_inner_component
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
      (source_a5_oddNormalizer_inner_of_smallFrattini D e hn hp B hB hBC hperm K P hP)

end CFSG.Quasithin.Chapter10

