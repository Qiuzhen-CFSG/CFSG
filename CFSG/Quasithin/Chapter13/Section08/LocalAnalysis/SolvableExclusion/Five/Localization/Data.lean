module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SupportActions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets

/-!
# Construction targets for the five-primary localization

`GeometricBounds` records the required output of critical-pair localization.
Every endpoint, edge, line and module is the actual construction from the
chosen coset-graph critical pair. `SecondFactor` records the output of the
subsequent actor construction on the supplied canonical five-factor supports.
Neither structure asserts existence. They are intermediate construction
targets; the localization assembly must produce both from the genuine
source setup, minimality, earlier results and the rank-one factor input.

The two constructions can be proved independently: the actor construction
may take the geometric bounds explicitly, and final assembly supplies them.
In particular the second actor is not an assumed contradiction witness:
its required properties are actual starred subgroup orders, product,
centralization and normalization statements.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, from “Therefore” through the last commutator calculation.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization
open Subgroup
open CriticalGeometry
variable {G : Type*} [Group G]

/-- Geometric output, tied to the original critical pair. The rank conclusion
is expressed as order greater than two for the elementary starred group. -/
structure GeometricBounds {L T H V : Subgroup G}
    (c : CriticalPair L T H V) (V₃ V₁ : Subgroup G) : Prop where
  Ugamma_le : c.Ugamma V₃ ≤ H
  Vgamma_le : c.Vgamma ≤ H
  Vone_le : V₁ ≤ Source.UH H V₃
  Aone_le : c.Aone V₁ ≤ Source.UH H V₃
  Aone_card : Nat.card (c.Aone V₁) = 2
  DH_index : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
    (Source.UH H V₃) = 2
  lines_disjoint : Disjoint V₁ (c.Aone V₁)
  centralizer_commutator :
    ⁅Source.UH H V₃ ⊓ centralizer (c.Ugamma V₃ : Set G), c.Vgamma⁆ ≤ c.Aone V₁
  endpoint_generation : vertexGroup L T H c.gamma =
    conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔
      edgeGroup L T H c.gamma c.previous
  Vgamma_star_card : 2 < Nat.card (Source.starImage H c.Vgamma)

variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

/-- Algebraic output on the actual factors. The second index is necessarily
one; keeping it explicit avoids selecting an unrelated second summand. -/
structure SecondFactor (a : StarAction H UH V₁) {P Uγ : Subgroup G}
    (f : RankOneFactors a P Uγ) (Vγ A₁ : Subgroup G) where
  count_eq_two : f.factors.count = 2
  second : Fin f.factors.count
  second_ne_zero : second.val ≠ 0
  B₂ : Subgroup G
  B₂_le : B₂ ≤ Vγ
  star_card : Nat.card (Source.starImage H B₂) = 2
  star_product : Source.starImage H Vγ = Source.starImage H Uγ ⊔ Source.starImage H B₂
  star_disjoint : Disjoint (Source.starImage H Uγ) (Source.starImage H B₂)
  star_commute : ⁅Source.starImage H Uγ, Source.starImage H B₂⁆ = ⊥
  centralizes_first : ⁅Source.starImage H B₂,
    Source.starImage H (f.factors.factor ⟨0, f.factors.count_pos⟩)⁆ = ⊥
  moves_second : ⁅Source.starImage H B₂,
    Source.starImage H (f.factors.factor second)⁆ ≠ ⊥
  normalizes_second : Source.starImage H Vγ ≤
    normalizer (Source.starImage H (f.factors.factor second) : Set _)
  line_le_first : tildeImage UH V₁ A₁ ≤ f.factors.support ⟨0, f.factors.count_pos⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization
end
