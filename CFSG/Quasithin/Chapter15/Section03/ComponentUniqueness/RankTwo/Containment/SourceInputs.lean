module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.PlaneGeometry

/-!
# Earlier source inputs for 15.3.39--40

These are the standing local conditions and the indicated conclusions of
15.3.7, 15.3.9, 15.3.11--12 and 15.3.33--38. The component alternative is
the relative normality/index/model alternative of 1.2.1(3). All subgroups,
actions, residuals and quotients are the actual constructions of `LocalData`.

The corrected three-part alternatives retain every clause except the printed
full-order assertion for the centralizer. Neither component-orbit equality,
an oriented plane, an A₄ actor, nor an alternating-square configuration is
assumed. The parent source assembly must supply these earlier results.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
pp.1121--1125 and 1134--1138; the 15.3.37 correction is documented in
`docs/quasithin-proof-basis.md`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- Earlier results consumed by the conditional source implications.
In particular `rank_two_containment` is exactly the earlier 15.3.38,
and is used only in its rank-two branch. -/
structure ContainmentSourceInputs (d : CharacteristicTwo.LocalData G)
    (I L : Subgroup G) (z : G) : Prop where
  outside : I ∈ d.Hplus
  characteristic_two : centralizer (pCore 2 d.M : Set d.M) ≤ pCore 2 d.M
  centralizer_overgroup : d.Mc = centralizer (d.Z : Set G)
  residual_image : d.action.image d.Y =
    Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)
  residual_core : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
    (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)
  residual_quotient : RankOne.PlaneGeometry.SourceQuotientAlternatives d.Y d.V
  not_alternating_square :
    ¬ Nonempty (d.Y ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4)))
  outside_structure : OutsideStructure.Conclusions d I
  rank_two_case : OutsideStructure.RankTwoCase d I
  component_le : L ≤ I
  component : IsComponent I (L.subgroupOf I)
  component_structure : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) d.M z
  strongly_quasithin : IsStronglyQuasithin I
  component_rank_pos : 1 ≤ primeRank 3 L
  residual_rank : primeRank 3 d.Yplus = 2
  component_alternative : (L.subgroupOf I).Normal ∨
    (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel
        ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I))
  invariant_subgroup : ∀ D : Subgroup G, D ≤ localSpan L d.S →
    d.Yplus ⊔ d.S ≤ normalizer (D : Set G) →
    generalizedFitting D = pCore 2 D → D ≤ d.M ⊓ I
  alternatives : Candidates.Alternatives15337ThreePart d.Yplus L (componentOrbit L d.S)
  rank_two_containment : primeRank 3 L = 2 → d.Yplus ≤ L
  intersection_splitting : primeRank 3 L = 1 →
    ComponentIntersection.InducesInnerOnTwoCoreQuotient d.Yplus L →
    (d.Yplus : Set G) =
      (ComponentIntersection.intersectionResidual d.Yplus L : Set G) *
        (ComponentIntersection.centralizerResidual d.Yplus L : Set G) ∧
    3 ^ (Nat.card (componentFactor d.Yplus L)).factorization 3 = 3 ∧
    Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3))

end CFSG.Quasithin.Chapter15.Section03.RankTwo
