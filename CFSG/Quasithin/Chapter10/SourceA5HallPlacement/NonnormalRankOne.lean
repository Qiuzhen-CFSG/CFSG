module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.RankOneComponents
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.NonnormalProjection

/-!
 # Rank-one exclusions for the actual nonnormal component

 The component itself is SQTK because of its distinct commuting conjugate.
 Its proved soluble outer group discharges the inner-action premise in the
 four concrete central-quotient exclusions. The residual and normalizer maps
 are those of the original Hall counterexample.

 Source: Aschbacher--Smith 4.4.9--11, printed p.621.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_oddNormalizer_no_sl2_nonnormal_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Theory.PSL2.Group F)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) : False := by
  exact source_oddNormalizer_no_sl2_component D B hBC hodd hBV K houtK e hFK
    (source_oddNormalizer_nonnormal_component_inner D B hne K hK hnK hFK)

theorem source_oddNormalizer_no_suzuki_nonnormal_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m)
    (e : K ⧸ center K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) : False := by
  exact source_oddNormalizer_no_suzuki_component D B hBC hodd hBV K houtK hm e hFK
    (source_oddNormalizer_nonnormal_component_inner D B hne K hK hnK hFK)

theorem source_oddNormalizer_no_prime_psl2_nonnormal_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 2 p)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) : False := by
  exact source_oddNormalizer_no_prime_psl2_component D B hBC hodd hBV K houtK hp ho hmodel hFK
    (source_oddNormalizer_nonnormal_component_inner D B hne K hK hnK hFK)

theorem source_oddNormalizer_no_janko_nonnormal_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (e : K ⧸ center K ≃* Janko1.Model)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) : False := by
  exact source_oddNormalizer_no_janko_component D B hBC hodd hBV K houtK e hFK
    (source_oddNormalizer_nonnormal_component_inner D B hne K hK hnK hFK)

end CFSG.Quasithin.Chapter10
