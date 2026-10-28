module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.SourceB4
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source
public import Theory.Representation.MathieuCodeRestriction.CodeLocal

/-!
# The ordinary M₂₂ exclusion in 13.8.21(2)

The standing setup retains an actual K/O₂(K) ≃ M₂₂, relative component
normality, the source Sylow arrangement, and the earlier solvable-overgroup
property. The seed hypotheses concern the literal V₃/V₁ and its conjugation
action on Source.Utilde. F.9.18(2–4),(7) and the full universal B.4
classifications remain explicit earlier source inputs.

The full B.4.2 list excludes every faithful FF-module. This eliminates
F.9.18(4ii); the concrete model comparisons eliminate (iii), giving the
invariant section I. F.9.18(7) gives I = [Ũ_H,K], and the actual offender
bound selects the code action on I/C_I(K) from the full B.4.5 table.
The rank-two seed injects equivariantly into this central quotient.

The terminal theorem constructs the actual hexad parabolic, compares the
two literal radicals and their actions, and restricts the proved M₂₄ octad
fixed line to the native ten-dimensional M₂₂ hyperplane. Thus the seed
would embed into a line. No splitting of I, preselected code module,
moved-space identity or additional fixed-line premise is assumed.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956, PDF p.973;
F.9.18, pp.325–326; B.4.2/B.4.5, pp.86–87; H.13.1 and H.16.2(1),
pp.395 and 402 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu

universe u
variable {G : Type u} [Group G] [Finite G]
  {H K L₁ T G₁ M V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The M₂₂ branch is impossible under the genuine earlier source inputs.
The full representation classifiers and F.9.18 outputs are explicit;
their specialized consequences, parabolic placement, seed embedding and
fixed-line comparison are all discharged in this proof. -/
theorem source_contradiction_of_earlier {𝒦 : GroupClass.{u}}
    (s : Placement.Setup H K L₁ T G₁ M) (d : SourceAction H V₃ V₁)
    (hH : IsSQTK 𝒦 H)
    (hB42 : Recognition.SourceB4.FullB42.{u,u} 𝒦) (hB45 : FullB45.{u,u} 𝒦)
    {L : Subgroup G} (hF918 : Recognition.F918Source.Earlier s d L)
    (hline : V₁ < V₃) (hindex : (V₁.subgroupOf V₃).index = 4)
    (hgen : ⁅V₃, L₁⁆ = V₃) (hn : L₁ ⊔ T ≤ normalizer (V₃ : Set G))
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      L₁ ⊔ T ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃) : False := by
  obtain ⟨w⟩ := Recognition.F918Source.centralWitness_of_earlier s d hH
    (Recognition.SourceB4.noFaithfulFF hB42)
    (Recognition.SourceB4.smallQuadraticCode hB42 hB45) hF918
  exact source_central_code_contradiction_of_group_seed H K L₁ T G₁ M V₃ V₁
    s d hline hindex hgen hn hirr w.I w.moved w.code MathieuCode.m24OctadFixedLine

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
