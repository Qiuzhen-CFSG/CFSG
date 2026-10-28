module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentClosure
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentNormalityComplete
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PairImage
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.CentralQuotientRank

/-!
# The actual normal-component placement alternative

The completed nonnormal-component inspection makes the selected component
normal. The original pair-image theorem then gives inner residual action or
an outer image divisible by twenty-five. Inner action, the full uniqueness
actor and the odd-centralizer argument place the residual and module in K.
This also forces two-rank at least eight in its literal central quotient.
The alternative requiring an outer-action obstruction remains explicit.

Source: Aschbacher--Smith4.4.10--12, printed pp.621--622.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Normality and the pair-image alternative reduce actual placement to
excluding a twenty-five divisor in the component's outer automorphism group. -/
theorem source_a5_oddNormalizer_component_placement_or_outer_twentyFive
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
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    K.Normal ∧
      ((D.fullModule.subgroupOf (normalizer (B : Set G)) ≤ K ∧
        centralizer (K : Set (normalizer (B : Set G))) =
          pPrimeCore 2 (normalizer (B : Set G)) ∧
        ((solvableResidual
          (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
            (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
              (normalizer (B : Set G)) ≤ K ∧
        8 ≤ primeRank 2 (K ⧸ center K)) ∨
      25 ∣ Nat.card (MulAut.Outer K)) := by
  let : K.Normal := source_a5_oddNormalizer_component_normal
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  refine ⟨inferInstance,?_⟩
  rcases source_a5_oddNormalizer_inner_or_twentyFive_outer
    D e hn hp B hB hBC hperm K with hi | ho
  · have hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
        normalizer (K : Set (normalizer (B : Set G))) := by
      intro y _
      exact le_normalizer_of_normal (mem_top y)
    obtain ⟨_,hV,hC,hF⟩ := source_a5_oddNormalizer_component_closure_of_overlap_normalizes
      D e hn hp B hB hBC hBV hperm K hK houtK hYK hi
    exact Or.inl ⟨hV,hC,hF,
      source_a5_oddNormalizer_component_centralQuotient_twoRank_ge_eight
        D e hn hp B hB hBC hBV hperm K hK houtK hF⟩
  · exact Or.inr (ho.trans (Subgroup.card_subgroup_dvd_card _))

/-- A hypothetical escaping odd actor has a normal Theorem B component;
it is placed with rank eight, or its outer group has a twenty-five divisor. -/
theorem source_a5_oddPrimeNormalizer_normal_component_alternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (hout : ¬ normalizer (B : Set G) ≤ D.maximalLocal) :
    ∃ K : Subgroup (normalizer (B : Set G)),
      IsComponent (normalizer (B : Set G)) K ∧ K.Normal ∧
      ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      ((((solvableResidual
        (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
          (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
            (normalizer (B : Set G)) ≤ K ∧
        8 ≤ primeRank 2 (K ⧸ center K)) ∨ 25 ∣ Nat.card (MulAut.Outer K)) := by
  obtain ⟨K,hK,_,houtK,hcore,_,_,hFK,_⟩ :=
    source_a5_oddPrimeNormalizer_moved_component D e hn hp B hne hB hBC hBV hperm hout
  obtain ⟨hKN,hh⟩ := source_a5_oddNormalizer_component_placement_or_outer_twentyFive
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  refine ⟨K,hK,hKN,houtK,hcore,source_oddNormalizer_component_theoremB D B hne K hK,?_⟩
  exact hh.imp (fun h => ⟨h.2.2.1,h.2.2.2⟩) id

end CFSG.Quasithin.Chapter10
