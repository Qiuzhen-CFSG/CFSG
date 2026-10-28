module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.Source
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.Complete

/-!
# Original linear recognition after the field and cover sieve

The completed original 13.8.19–21 sieve supplies ComponentConclusions on
every member of the actual Hz family. Applying it to the uniform A₇
exclusion and binary reduction discharges the last component premise of
13.8.25. Both critical cases give the covered local quotient, H* ≃ L₄(2),
H = G₁, and compatible natural coordinates on the whole U_H/V₁.

The final application constructs the action from conjugation and states
equivariance on the literal quotient map. Thus no representation or
component conclusion is an extra input. The genuine EarlierInputs,
EarlierLocalInputs, G.6.4, original LocalSetup, F.9 and 13.3.9 hypotheses
remain explicit; their discharge belongs to the original 13.8.1 assembly.

Source: Aschbacher–Smith, 13.8.24–25, printed pp.958–962/PDF pp.975–979.
-/

public section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FourStructure.ChiefFactors SourceCompletion
open Chapter1.Section02.LocalModels Chapter2.ComponentRefinement.LieType.Binary
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
  (localEarlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G))
  (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
  (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)

include d earlier localEarlier hG64 hmax hF9all hcentral hcomm hsource

/-- Uniform original 13.8.24 after constructing the preceding component conclusions. -/
theorem original_not_alternatingSeven
    {H K : Subgroup G} (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    ¬ IsAlternating (K ⧸ pCore 2 K) 7 := by
  exact not_alternatingSeven_source d earlier localEarlier hG64 hmax hF9all
    hcentral hcomm hsource
    (FieldComponents.LinearThree.OriginalExclusion.original_component_conclusions
      d hmax hF9all hcentral hcomm) hH hKH hK

/-- The actual quotient and overgroup conclusions, with the field sieve discharged. -/
theorem original_linear_reduction
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) :
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty (Source.Hstar H ≃* PSL 4) ∧ H = G₁ := by
  exact source_linear_reduction d earlier localEarlier hG64 hmax hF9all
    hcentral hcomm hsource
    (FieldComponents.LinearThree.OriginalExclusion.original_component_conclusions
      d hmax hF9all hcentral hcomm) hH hKH hK hn₀ hn₁ hmodel

/-- Original 13.8.25 for any representation realizing the literal source action.
The field and cover sieve supplies all preceding component conclusions. -/
theorem original_linear_alternative
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) :
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Nonempty (Source.Hstar H ≃* PSL 4) ∧
      (∃ (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
        (eU : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] NaturalSpace),
        (∀ a v, eU (ρ a v) = eH a (eU v)) ∧
        Module.finrank (ZMod 2) (SourceSpace H V₃ V₁) = 4) ∧ H = G₁ := by
  exact source_linear_alternative d earlier localEarlier hG64 hmax hF9all
    hcentral hcomm hsource
    (FieldComponents.LinearThree.OriginalExclusion.original_component_conclusions
      d hmax hF9all hcentral hcomm) hH hKH hK hn₀ hn₁ hmodel ρ hρ

/-- Original 13.8.25 on the actual conjugation quotient, with its action and
elementary-abelian structure constructed from the preceding local setup. -/
theorem original_linear_recognition
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) :
    letI := d.uh_elementary hH
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Nonempty (Source.Hstar H ≃* PSL 4) ∧
      (∃ (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
        (eU : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] NaturalSpace),
        (∀ (h : H) (v : Source.UH H V₃),
          eU (Additive.ofMul (sourceProjection H V₃ V₁ (sourceConjugate H V₃ h v))) =
            eH (QuotientGroup.mk' (pCore 2 H) h)
              (eU (Additive.ofMul (sourceProjection H V₃ V₁ v)))) ∧
        Module.finrank (ZMod 2) (SourceSpace H V₃ V₁) = 4) ∧ H = G₁ := by
  let := d.uh_elementary hH
  have hF9 := hF9all H hH
  let act := Comparison.conjugationAction (d.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  have hact : IsSourceAction H V₃ V₁ act.representation := act.conjugation
  obtain ⟨hn, hcover, hL, hHstar, ⟨eH, eU, heq, hdim⟩, hHG⟩ :=
    original_linear_alternative d earlier localEarlier hG64 hmax hF9all
      hcentral hcomm hsource hH hKH hK hn₀ hn₁ hmodel act.representation hact
  refine ⟨hn, hcover, hL, hHstar, ⟨eH, eU, ?_, hdim⟩, hHG⟩
  intro h v
  rw [← hact h v]
  exact heq _ _

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
