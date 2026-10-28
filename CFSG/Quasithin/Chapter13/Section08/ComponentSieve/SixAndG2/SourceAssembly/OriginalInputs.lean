module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.Complete

/-!
# Applying the completed component, field and linear source reductions

The original 13.8.19–25 theorems construct the uniform survivor catalogue,
relative normality, supplement and full natural L₄ action. The actual Sylow
image and quasisimple component identify F*(H*) with K*. The field theorem
also supplies U_H=[U_H,K]. G.6.4 and the original residual input are proved
inputs here; neither is an additional hypothesis.

These are the precise premises used by `SourceAssembly.Original`. The
original local setup, maximal-local, universal F.9 and 13.7.6 hypotheses
retain their producers and final discharge with qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.19–25, printed pp.953–962.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open CriticalGeometry SourceCompletion
open FieldComponents.HigherFieldReduction.ExternalModules
open AlternatingAndLinear.FourStructure.CriticalTransfer
open AlternatingAndLinear.LinearReduction.Overgroup
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L H K V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- Supply the complete uniform quotient sieve from its original source producers. -/
theorem original_uniform_component_facts
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    UniformComponentFacts L (sourceOne L T V₁) T G₁ M := by
  have components := FieldComponents.LinearThree.OriginalExclusion.original_component_conclusions
    d hmax hF9all hcentral hcomm
  have groups := FieldComponents.LinearThree.OriginalExclusion.original_linear_group_facts
    d hmax hF9all hcentral hcomm
  have residual := Components.EarlierResidual.original_source d hmax
  have g64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple :=
    FieldComponents.LinearThree.OriginalExclusion.g64_source_knownSimple
  refine {
    base_le := components.base_le
    componentList := components.models
    join_eq := groups.supplement
    normal := groups.component_normal
    not_A7 := fun hJ hCJ hC =>
      AlternatingAndLinear.LinearReduction.OriginalSource.original_not_alternatingSeven
        d earlier localEarlier g64 hmax hF9all hcentral hcomm residual hJ hCJ hC
    binaryReduction := ?_ }
  intro J C n hJ hCJ hC hn₀ hn₁ hmodel
  obtain ⟨hn, hc, ⟨eJ⟩, _⟩ :=
    AlternatingAndLinear.LinearReduction.OriginalSource.original_linear_reduction
      d earlier localEarlier g64 hmax hF9all hcentral hcomm residual
      hJ hCJ hC hn₀ hn₁ hmodel
  exact ⟨hn, hc, ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ⟨eJ⟩⟩⟩

/-- Retain the covered local quotient and full equivariant L₄ action on U_H/V₁. -/
theorem original_linear_models
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      HasActionModel ρ projectiveFourRepresentation := by
  obtain ⟨_, _, hL, _, ⟨eH, eU, he, _⟩, _⟩ :=
    AlternatingAndLinear.LinearReduction.OriginalSource.original_linear_alternative
      d earlier localEarlier
      FieldComponents.LinearThree.OriginalExclusion.g64_source_knownSimple
      hmax hF9all hcentral hcomm (Components.EarlierResidual.original_source d hmax)
      hH hKH hK (by decide : 3 ≤ 4) (by decide : 4 ≤ 5) hmodel ρ hρ
  refine ⟨hL, eH.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide)).symm,
    eU, ?_⟩
  intro a v
  change eU (ρ a v) =
    ((BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))
      ((BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)).symm (eH a))) (eU v)
  rw [MulEquiv.apply_symm_apply]
  exact he a v

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- Identify the actual generalized Fitting subgroup, commutator and Sylow supplement. -/
theorem original_component_structure
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    generalizedFitting (Source.Hstar H) = Source.starImage H K ∧
      Source.UH H V₃ = ⁅Source.UH H V₃, K⁆ ∧
      ∃ P : Sylow 2 (Source.Hstar H), Source.starImage H K ⊔ (P : Subgroup _) = ⊤ := by
  have groups := FieldComponents.LinearThree.OriginalExclusion.original_linear_group_facts
    d hmax hF9all hcentral hcomm
  let : (K.subgroupOf H).Normal := groups.component_normal hHz hKH hK
  let : (Source.starImage H K).Normal :=
    FieldComponents.SmallCovers.Reduction.ModuleRecognition.Selection.starImage_normal H K
  let : IsQuasisimple (Source.starImage H K) :=
    (SolvableSource.component_fitting_source d hmax hF9all hcentral hcomm
      (Components.EarlierResidual.original_source d hmax) hHz K hK).2
  obtain ⟨P, hPT⟩ := FieldComponents.LinearThree.Geometry.ParabolicMarking.starImage_sylow
    H T (le_sup_right.trans hHz.1.2)
  have hP : Source.starImage H K ⊔ (P : Subgroup (Source.Hstar H)) = ⊤ :=
    FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.star_sylow_generation
      H K (T : Subgroup G) (groups.supplement hHz hKH hK) P hPT
  have hquot : IsPGroup 2 (Source.Hstar H ⧸ Source.starImage H K) :=
    isPGroup_quotient_of_sup_eq_top (Source.starImage H K)
      (P : Subgroup (Source.Hstar H)) P.isPGroup' hP
  exact ⟨generalizedFitting_eq_of_quasisimple_two_quotient _ hquot
      (pCore_quotient_pCore_eq_bot 2),
    (FieldComponents.HigherFieldReduction.OriginalSource.original_component_consequences
      d hmax hF9all hcentral hcomm hHz hKH hK).2.2.2, P, hP⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
