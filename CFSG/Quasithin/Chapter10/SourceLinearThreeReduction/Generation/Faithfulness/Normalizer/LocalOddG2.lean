module
public import Theory.SpecificGroups.G2.OddFrattiniSixteen
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalSmallDegree

/-!
# Excluding odd prime-field G₂ normalizer components

The Sylow Frattini bound places the original residual inside the full covering
component. The actual split-octonion representation then gives the faithful
eight-dimensional representation of its central quotient needed by the
small-degree automizer contradiction. The covering center is retained.

Source: the G₂ row of Aschbacher--Smith Theorem B in the 4.4.3 argument,
printed p.622, as used in 10.2.3(2), printed p.745. The imported octonion
construction retains its ATLAS attribution and license.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The split-octonion action excludes an odd G₂ component containing the actual residual. -/
theorem source_nonnormal_oddNormalizer_no_placed_odd_g2_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G) (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (V : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hc : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {r : ℕ} (ho : Odd r) (hm : ClassificationModels.IsG2At (K ⧸ center K) r) : False := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let σ : Representation F (Atlas.G2.Model F) (Atlas.SplitOctonion.Carrier F) := {
    toFun := fun g => (Atlas.G2.representation F g).toLinearMap
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hσ : Function.Injective σ := by
    intro a b h
    exact Atlas.G2.representation_injective F (LinearEquiv.toLinearMap_injective h)
  exact source_nonnormal_oddNormalizer_no_placed_small_degree_component D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hc hFK
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card
      (k := 1) ho (by simpa only [pow_one] using hF))
    (σ.comp e.toMonoidHom) (hσ.comp e.injective)
    (by rw [Atlas.G2.carrier_finrank])

/-- The Frattini placement theorem discharges the residual premise for odd prime-field G₂. -/
theorem source_nonnormal_oddNormalizer_no_odd_g2_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (V : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hc : pCore 2 K = ⊥) {r : ℕ} [Fact r.Prime] (ho : Odd r)
    (hm : ClassificationModels.IsG2At (K ⧸ center K) r) : False := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hbound : ∃ P : Sylow 2 (K ⧸ center K), Nat.card (P ⧸ frattini P) ≤ 32 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    refine ⟨P,?_⟩
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr
      (e.subgroupMap (P : Subgroup _))]
    exact (Atlas.G2.OddFrattiniSixteen.frattini_card_le_sixteen ho hF Q).trans (by decide)
  obtain ⟨P,hP⟩ := hbound
  exact source_nonnormal_oddNormalizer_no_placed_odd_g2_component D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hc
    (source_local_oddPrimeActor_residual_le_of_smallFrattini
      D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout P hP) ho hm

end CFSG.Quasithin.Chapter10.LocalFixed
