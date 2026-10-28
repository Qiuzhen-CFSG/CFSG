module

public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.OddInner
public import Theory.SpecificGroups.G2.OddSylowFrattini
public import Theory.GroupTheory.SylowFrattiniBounds

/-!
# Inner action on the odd prime-field G₂ Hall component

The actual G₂ model supplies a Sylow Frattini quotient of order at most
128. Transport this bound across the original central-quotient marking
and apply the pair's Sylow restriction theorem. The resulting inner action,
together with the proved normality and placed-component inspection, excludes
the G₂ row of the odd Theorem B catalogue.

Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The original residual acts innerly on a normal quasisimple component
whose actual central quotient is G₂ over an odd prime field. -/
theorem source_a5_oddNormalizer_inner_of_odd_g2
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) [K.Normal] [IsQuasisimple K]
    {r : ℕ} [Fact r.Prime] (hr : Odd r)
    (hmodel : IsG2At (K ⧸ center K) r) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  apply source_a5_oddNormalizer_inner_of_smallFrattini D e hn hp B hB hBC hperm K P
  obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hmodel
  let Q : Sylow 2 (Atlas.G2.Model F) :=
    P.mapSurjective (f := a.toMonoidHom) a.surjective
  have ha : P ≃* Q := P.equivMapOfInjective a.toMonoidHom a.injective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr ha]
  exact Atlas.G2.OddSylowFrattini.frattini_card_le hr hF Q

/-- The odd prime-field G₂ row is impossible for the original selected
Hall component; no Sylow bound or inner-action premise remains. -/
theorem source_a5_oddNormalizer_no_odd_g2_component
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
    {r : ℕ} [Fact r.Prime] (hr : Odd r)
    (hmodel : IsG2At (K ⧸ center K) r) : False := by
  let : K.Normal := source_a5_oddNormalizer_component_normal
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  let : IsQuasisimple K := hK.2
  exact source_a5_oddNormalizer_no_inner_component
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
      (source_a5_oddNormalizer_inner_of_odd_g2 D e hn hp B hB hBC hperm K hr hmodel)

/-- Every odd Theorem B row is excluded for the original selected Hall
component, including the exceptional prime-field G₂ row. -/
theorem source_a5_oddNormalizer_no_odd_component
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
    (hmodel : IsTheoremBOddModel (K ⧸ center K)) : False := by
  obtain ⟨r, hr, ho, hm⟩ := source_a5_oddNormalizer_odd_component_g2
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK hmodel
  let : Fact r.Prime := ⟨hr⟩
  exact source_a5_oddNormalizer_no_odd_g2_component
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK ho hm

end CFSG.Quasithin.Chapter10
