module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.Final
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.TerminalModels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.CoveredSetup

/-!
# Terminal applications of the source dichotomy

Apply the completed conditional 13.8.27 dichotomy to the literal star
action. In the ordinary branch, construct the base-edge syntheme marking
and compatible natural or augmentation plane used by 13.8.34. In the
covered branch, construct the original covered local flag, full L₄ action
and the order of the endpoint module used by 13.8.29–32.

The independent preceding component, field, linear and universal 13.7.6
inputs still belong to their original producers and qt-d-1381-source.
The subsequent ordinary and covered terminal exclusions retain their
existing owners; no assertion here completes those source arguments.
Source: Aschbacher–Smith, 13.8.27–34, printed pp.963–969.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open CriticalGeometry CriticalGeometry.AsymmetricPair SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open AlternatingAndLinear.LinearReduction.Overgroup
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L H K V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Construct the ordinary and covered terminal inputs from the actual
source reductions; all component, group and module markings are retained. -/
theorem source_terminal_setups
    (embeddings : EarlierEmbeddings.{u} KnownSimple.IsKnownSimple)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (earlierFlags : TransvectionParabolic.Marking.NaturalSection.Earlier1376 L
      (sourceOne L T V₁) (T : Subgroup G) G₁ M V₂ V₃ V₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (P : Sylow 2 (Source.Hstar H))
    (hP : Source.starImage H K ⊔ (P : Subgroup _) = ⊤)
    (orbit : letI : (Source.starImage H K).Normal := hfit ▸ inferInstance
      OrbitInputs (A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a) (Source.starImage H K) P hP)
    (linear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2 →
      HasActionModel (A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a) projectiveFourRepresentation) :
    let ρ := A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a
    G₁ = H ∧ H = K ⊔ (T : Subgroup G) ∧
      ((∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
          HasSectionModel H V₃ V₁ ρ K hKH
            (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK ∧
          Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
          SourceSix.MarkedFullAction hKH eK ρ ∧
          Reorientation.TwoNoncentralChiefFactors
            (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
              (le_sup_left.trans hHz.1.2) ρ) ∧
          TerminalRanks.MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁) ∨
        (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
          Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) ∧
          HasActionModel ρ linearFourRepresentation ∧
          Nat.card (Source.UH H V₃) = 32 ∧ rank (Source.UH H V₃) = 5 ∧
          ∀ c : CriticalPair L (T : Subgroup G) H V, Nat.card (c.Ugamma V₃) = 32)) := by
  let ρ := A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a
  have hd := source_dichotomy embeddings d earlier localEarlier facts hHz hF9 hKH hK
    hfit hUK hcentral hcomm ρ (TerminalPoint.starAction_isConjugation a) P hP orbit linear
  refine ⟨hd.2.2.1, hd.2.2.2.1, ?_⟩
  rcases hd.2.2.2.2.2 with h6 | h4
  · obtain ⟨eK, hs, hL, hm, hchief⟩ := h6
    exact Or.inl ⟨eK, hs, hL, hm, hchief,
      TerminalModels.ordinary_terminal_models d earlierFlags hHz hF9 hcomm hKH hK
        (facts.normal hHz hKH hK) hd.2.2.2.1 a eK hs⟩
  · exact Or.inr ⟨h4.1, covered_terminal_setup d h4.1 ρ h4.2⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
