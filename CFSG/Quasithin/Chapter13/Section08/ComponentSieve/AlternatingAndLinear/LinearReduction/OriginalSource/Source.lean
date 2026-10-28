module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.Recognition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.B4

/-!
# Original 13.8.25 after the preceding component and field conclusions

Apply the proved marked B.4 theorems to the actual H* and K*, discharging
the last two inputs of the middle-node quotient argument. Both original
critical cases are retained. The resulting theorem includes n = 4, the
actual covered local model, H* ≃ L₄(2), an equivariant identification of the
whole literal U_H/V₁ with the natural four-space, and H = G₁.

There is no local geometry, group-classification, representation-classification
or middle-node callback. The genuine preceding source assumptions and
ComponentConclusions of 13.8.21 remain explicit; qt-d-138-fields-source
supplies the latter and qt-d-1381-source retains the earlier source assembly.
The linear source task must await these inputs before unconditional completion.

Source: Aschbacher–Smith, 13.8.25, printed pp.959–962/PDF pp.976–979.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
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
  (components : ComponentConclusions (one L T V₁) T G₁ M)

include d earlier localEarlier hG64 hmax hF9all hcentral hcomm hsource components

/-- The marked S₈ middle node is excluded on every actual source overgroup.
The preceding component conclusions supply relative normality and the supplement;
the two marked B.4 classifications are proved here. -/
theorem middle_node_exclusion
    {H K : Subgroup G}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (e : (K ⧸ pCore 2 K) ≃* PSL 4) :
    ¬ Parabolics.MiddleNodeMarking H K (one L T V₁) T hKH hK e := by
  have groups := group_facts d hmax hF9all hcentral hcomm hsource components
  exact middle_node_exclusion_of_b4 d earlier localEarlier hG64 hH (hF9all H hH)
    hcentral hcomm hKH hK (groups.component_normal hH hKH hK)
    (components.base_le hH hKH hK) (groups.supplement hH hKH hK).symm
    (fun eH hK => symmetric_b4 (Source.starImage H K) eH hK)
    (fun eH eK hK => component_b4 (Source.starImage H K) eH eK hK) e

/-- The binary quotient and actual overgroup conclusions of 13.8.25.
Both the middle-node and uniform A₇ exclusions are discharged. -/
theorem source_linear_reduction
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) :
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty (Source.Hstar H ≃* PSL 4) ∧ H = G₁ := by
  exact source_linear_reduction_of_middle_exclusion d hmax hF9all hcentral hcomm
    hsource components
    (fun _ _ hJ hCJ hC e => middle_node_exclusion d earlier localEarlier hG64 hmax
      hF9all hcentral hcomm hsource components hJ hCJ hC e)
    (fun hJ hCJ hC => not_alternatingSeven_source d earlier localEarlier hG64 hmax
      hF9all hcentral hcomm hsource components hJ hCJ hC) hH hKH hK hn₀ hn₁ hmodel

/-- All original linear-branch conclusions, with both marked B.4 inputs
proved and applied to the literal source quotient. Only the genuine preceding
source and 13.8.21 assumptions remain. -/
theorem source_linear_alternative
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
  exact source_linear_alternative_of_middle_exclusion d earlier localEarlier hG64 hmax
    hF9all hcentral hcomm hsource components
    (fun _ _ hJ hCJ hC e => middle_node_exclusion d earlier localEarlier hG64 hmax
      hF9all hcentral hcomm hsource components hJ hCJ hC e) hH hKH hK hn₀ hn₁ hmodel ρ hρ

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
