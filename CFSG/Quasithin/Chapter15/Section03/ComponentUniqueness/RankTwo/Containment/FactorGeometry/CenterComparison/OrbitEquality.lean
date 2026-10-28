module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.CenterComparison
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.OrbitEquality

/-!+# Applying the source center comparison to the orbit argument

The genuine 15.3.33(3), 15.3.34 and local SQTK inputs now discharge the
center/rank premise of the projection contradiction. In a strict orbit,
the complete 1.2.1(3) conclusion gives normalizer index two, with its quotient
taken by the actual two-core. The Sylow subgroup is realized inside I.

The parent assembly still supplies the plane actors, the inner-action
consequence of 15.3.12(2), and the orbit-containment consequence of 15.3.37.
This theorem discharges the comparison and index premises, rather than
asserting that these remaining source constructions have been completed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.2.1(3),
printed p.504; 15.3.39, printed pp.1137--1138.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- The orbit-equality consumer with the center/rank comparison and index bound
discharged from the earlier source conclusions. The remaining actor and residual
inputs are the independent geometry owned by the parent assembly. -/
theorem componentOrbit_eq_of_source_comparison_of_planeActors
    {M Y Yplus L I S V V₁ V₂ : Subgroup G} {z : G}
    (hLI : L ≤ I) (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I))
    (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) M z)
    (hSQT : IsStronglyQuasithin I) (h34 : 1 ≤ primeRank 3 L)
    (h121 : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel
          ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hSV₂ : S ≤ normalizer (V₂ : Set G))
    (hYV₂ : Yplus ≤ normalizer (V₂ : Set G))
    (hVS : V ≤ S) (hV₂ne : V₂ ≠ ⊥)
    (h37 : Yplus ≤ componentOrbit L S ∨ L = componentOrbit L S)
    (h12 : primeRank 3 L = 1 →
      ComponentIntersection.InducesInnerOnTwoCoreQuotient Yplus L →
      Yplus = ComponentIntersection.intersectionResidual Yplus L ⊔
        ComponentIntersection.centralizerResidual Yplus L ∧
      3 ^ (Nat.card (componentFactor Yplus L)).factorization 3 = 3 ∧
      Nat.card (Yplus ⧸ pCore 2 Yplus) = 9)
    (actors : PlaneActorPair M Y Yplus S V V₁ V₂) :
    L = componentOrbit L S := by
  classical
  by_cases heq : L = componentOrbit L S
  · exact heq
  have hlt := lt_of_le_of_ne (le_componentOrbit L S) heq
  have hindex := (nonnormal_model_of_strict_componentOrbit hLI P hP h121 hlt).1.le
  have hSI : S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  exact componentOrbit_eq_of_centerless_comparison_of_planeActors
    hLI hSI hL hindex hSY hSV₂ hYV₂ hVS hV₂ne h37 h12
    (centerless_comparison_of_source_inputs hLI P hP hL h33 hSQT h34) actors

end CFSG.Quasithin.Chapter15.Section03.RankTwo
