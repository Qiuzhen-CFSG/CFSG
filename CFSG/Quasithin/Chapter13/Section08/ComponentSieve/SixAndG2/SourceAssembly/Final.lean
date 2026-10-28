module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.Symmetry

/-!
# The three clauses of original 13.8.27

The source quotient sieve, both A₆ module cases and the derived-G₂
contradiction give the marked dichotomy and G₁=H=KT. Those actual module
models discharge the model premise in denominator symmetry for every
original critical pair. The conjugator, transported line, quotient action
and component markings are unchanged.

The preceding component, field and 13.8.25 linear conclusions remain
explicit independent source inputs. Their producers and the original
ambient setup are assembled by qt-d-1381-source; this theorem does not
claim those earlier stages have been discharged.
Source: Aschbacher–Smith, 13.8.26–27, printed pp.962–963.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open CriticalGeometry SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open AlternatingAndLinear.LinearReduction.Overgroup
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L H K V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- All three source clauses, conditional on the genuinely earlier source
reductions. The case-one conclusion refers to the unchanged critical pair. -/
theorem source_dichotomy_and_symmetry
    (embeddings : EarlierEmbeddings.{u} KnownSimple.IsKnownSimple)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (P : Sylow 2 (Source.Hstar H))
    (hP : Source.starImage H K ⊔ (P : Subgroup _) = ⊤)
    (orbit : letI : (Source.starImage H K).Normal := hfit ▸ inferInstance
      OrbitInputs ρ (Source.starImage H K) P hP)
    (linear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2 →
      HasActionModel ρ projectiveFourRepresentation) :
    ((K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      G₁ = H ∧ H = K ⊔ (T : Subgroup G) ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      ((∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
          HasSectionModel H V₃ V₁ ρ K hKH
            (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK ∧
          Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
          SourceSix.MarkedFullAction hKH eK ρ ∧
          Reorientation.TwoNoncentralChiefFactors
            (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
              (le_sup_left.trans hHz.1.2) ρ)) ∨
        (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
          HasActionModel ρ projectiveFourRepresentation))) ∧
    (∀ c : CriticalPair L (T : Subgroup G) H V,
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∨
        Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) →
    let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ ∧
      ⁅V, c.Ugamma V₃⁆ = V₁ ∧ V₁ ≤ c.Ugamma V₃ ∧ ¬ c.Vgamma ≤ Source.QH H ∧
      ∃ action : V →* MulAut (c.Ugamma V₃),
        (∀ v : V, ∀ u : c.Ugamma V₃,
          (action v u : G) = (v : G) * (u : G) * (v : G)⁻¹) ∧
        (∃ v : V, action v ≠ 1) ∧
        (∀ v : V, binaryLinear (action v) ∈
          LinearEquiv.transvections (ZMod 2) (Additive (c.Ugamma V₃)))) := by
  have result := source_dichotomy embeddings d earlier localEarlier facts hHz hF9
    hKH hK hfit hUK hcentral hcomm ρ hρ P hP orbit linear
  refine ⟨result, ?_⟩
  have models : (∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      HasSectionModel H V₃ V₁ ρ K hKH
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK) ∨
      HasActionModel ρ projectiveFourRepresentation := by
    rcases result.2.2.2.2.2 with hs | hl
    · obtain ⟨eK, hs, _⟩ := hs
      exact Or.inl ⟨eK, hs⟩
    · exact Or.inr hl.2
  intro c hcase
  exact source_case_one_of_survivor_models embeddings d facts hHz hF9 hKH hK hUK
    hcentral ρ hρ models c hcase

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
