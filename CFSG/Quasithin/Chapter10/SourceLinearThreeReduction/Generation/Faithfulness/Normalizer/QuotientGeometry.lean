module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.PairQuotient
public import Theory.GroupTheory.CentralQuotientLocalMarking
public import Theory.Quasithin.LocalRank

/-!
# Odd ranks in the actual normalizer component's central quotient

The residual covering L₀ retains the product of the original simple
component quotients. Its central-quotient map in a containing component
therefore has a two-group kernel. The original nontrivial moved module
also survives this map, supplying a genuine two-local normalizer whose
perfect subgroup has rank at least two at every odd component prime.
This is the input used by the rank-two binary model exclusions.

Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, applied to
10.2.3(2), p.745. No A₅ marking or centerless ambient component is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual residual and moved module retain their ranks and action in K/Z(K). -/
theorem source_nonnormal_oddNormalizer_component_quotient_geometry
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    let N := normalizer (B : Set G)
    let F := ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
    let P := F.subgroupOf K
    let W := (D.fullModule.subgroupOf N).subgroupOf K
    let q := QuotientGroup.mk' (center K)
    Group.IsPerfect (P.map q) ∧ W.map q ≠ ⊥ ∧
      IsElementaryAbelian 2 (W.map q) ∧ W.map q = ⁅W.map q,P.map q⁆ ∧
      P.map q ≤ normalizer (W.map q : Set (K ⧸ center K)) ∧
      ∀ p : ℕ, p.Prime → Odd p →
        primeRank p (P.map q) = 2 * primeRank p (L ⧸ pCore 2 L) := by
  let N := normalizer (B : Set G)
  let F := (solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let P := (F.subgroupOf N).subgroupOf K
  let W := (D.fullModule.subgroupOf N).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  obtain ⟨hP,_,_,hW,hE,_,hm,_,⟨a⟩⟩ :=
    source_oddNormalizer_component_local_geometry_of_residual_le D B hBC hodd hBV K hFK
  let : Group.IsPerfect P := hP
  obtain ⟨b⟩ := source_nonnormal_orbit_product_equiv D hn
  have hc : center (P ⧸ pCore 2 P) = ⊥ := by
    have ht : center ((L ⧸ pCore 2 L) × (L ⧸ pCore 2 L)) = ⊥ := by
      rw [Subgroup.center_prod,source_nonnormal_component_core_center D hn]
      exact bot_prod_bot
    apply bot_unique
    intro z hz
    have hz' := (centerCongr (a.trans b) ⟨z,hz⟩).property
    change (a.trans b) z ∈ center ((L ⧸ pCore 2 L) × (L ⧸ pCore 2 L)) at hz'
    rw [ht,mem_bot] at hz'
    exact mem_bot.mpr ((a.trans b).injective (hz'.trans (map_one (a.trans b)).symm))
  obtain ⟨hp,hne,he,hmove,hnorm⟩ := CentralQuotientLocalMarking.moved_image P W hW hE hm
  refine ⟨hp,hne,he,hmove,hnorm,?_⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  rw [CentralQuotientLocalMarking.primeRank_map P hc ho,
    ←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 P) pCore_isPGroup,
    primeRank_congr p (a.trans b),primeRank_prod_eq_add,two_mul]

/-- Every original odd component prime forces local rank at least two in K/Z(K). -/
theorem source_nonnormal_oddNormalizer_component_local_rank_ge_two
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    2 ≤ twoLocalPrimeRank p (K ⧸ center K) := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := F.subgroupOf K
  let W := (D.fullModule.subgroupOf N).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  obtain ⟨_,hne,he,_,hnorm,hr⟩ :=
    source_nonnormal_oddNormalizer_component_quotient_geometry D hn B hBC hodd hBV K hFK
  let : IsElementaryAbelian 2 (W.map q) := he
  have hl : IsTwoLocal (normalizer (W.map q : Set (K ⧸ center K))) :=
    ⟨W.map q,hne,IsElementaryAbelian.isPGroup 2 (W.map q),rfl⟩
  have hpos : primeRank p (L ⧸ pCore 2 L) ≠ 0 :=
    fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hd
  calc
    2 ≤ primeRank p (P.map q) := by rw [hr p Fact.out hp]; omega
    _ ≤ primeRank p (normalizer (W.map q : Set (K ⧸ center K))) := primeRank_mono p hnorm
    _ ≤ twoLocalPrimeRank p (K ⧸ center K) := hl.primeRank_le p

end CFSG.Quasithin.Chapter10
