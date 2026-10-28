module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NormalizerTheta
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.RankOne

/-!
# Literal section-normalizer application of13.7.5(3),(4)

The normalizer of V₃/V₁ in H/V₁, pulled back along the original quotient
map, is exactly the ambient normalizer of V₃. The source normalizer and
rank-two theta conclusions therefore apply to the literal section used
by the module exclusions, with no quotient convention left implicit.

Source: Aschbacher–Smith,13.7.5(3),(4) and13.7.6, pp.938–939.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf H).Normal]
include d

/-- The literal section-normalizer form of original13.7.5(3). -/
theorem seed_section_normalizer_le_local
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hV₃H : V₃ ≤ H) : seedSectionNormalizer H H V₃ V₁ ≤ M := by
  rw [seedSectionNormalizer_eq H H V₃ V₁ le_rfl hV₃H
    (d.line_le_plane.trans d.plane_le_seed)]
  exact seed_normalizer_le_local d hH hcentral

/-- Original13.7.5(4) on the exact H/V₁ section, for either original seed choice. -/
theorem covered_and_theta_of_section_normalizer_rank_two
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hX : sourceOne L T V₁ ≤ K ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ plus L T V₁ ≤ K))
    (hrank : primeRank 3 (seedSectionNormalizer H K V₃ V₁) = 2) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      closure {x : G | x ∈ seedSectionNormalizer H K V₃ V₁ ∧ orderOf x = 3} =
        sourceOne L T V₁ := by
  have hV₃H : V₃ ≤ H := hF9.plus_le_H
  rw [seedSectionNormalizer_eq H K V₃ V₁ hKH hV₃H
    (d.line_le_plane.trans d.plane_le_seed)] at hrank ⊢
  rcases hX with ho | ⟨hc, hx⟩
  · exact covered_and_theta_of_one_le_rank_two d h hH hF9 hcentral hKH hK ho hrank
  · exact ⟨hc, theta_of_plus_le_rank_two d h hH hF9 hcentral hc hKH hK hx hrank⟩

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
