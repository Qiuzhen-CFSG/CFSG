module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.ComponentContainment
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.ContainedRows
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import Theory.Representation.BinaryLinearNormalizerResidual

/-!
# Original containment and exclusion of the binary linear component rows

The natural SLₙ(2) and irreducible ten-dimensional SL₅(2) models have their
full linear normalizer's two-residual inside the component image. Apply
these concrete bounds to the original marked raw section and faithful
ambient extension to obtain actual point-residual containment L₁≤K.
A degree-one field is transported together with its natural action.

With this containment established, the original ordinary A₆ block and
noncentral plane hypotheses feed the existing contained-row arguments.
They exclude natural degree four, natural degree five, and dimension ten
without leaving point-residual containment as an additional premise.
The original selected source packet and its literal quotient maps are
retained throughout.

Source: Aschbacher–Smith, 13.7.6, printed pp.938–940, and the ordinary
model sieve in 13.7.18, printed p.945.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.Source Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.ModelExtension
open ChapterF.Section09.Setup
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
variable
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hsquare : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (hKH : K ≤ H) (hKC : (K.subgroupOf H).IsCComponent)
    (hKstar : IsComponent (Section08.Source.Hstar H) (Section08.Source.starImage H K))
    (hKn : H ≤ normalizer (K : Set G))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
include d hH h hU hV hne g hsquare hout σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ c

/-- The marked binary natural component contains the actual point residual. -/
theorem source_binary_natural_containment (n : ℕ)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (specialLinearNatural n) eK) :
    sourceOne L T V₁ ≤ K :=
  source_component_containment_of_model_residual d hH h hU hV hne g hsquare hout σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ
    (specialLinearNatural n) (specialLinearNatural_injective n) eK hs c
    (BinaryLinearNormalizerResidual.natural_residual_le n)

/-- The dimension-only exterior row has the same original containment. -/
theorem source_binary_ten_containment
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) SL5TenDimensional.Group E) [IsIrreducible τ]
    (hτ : Function.Injective τ) (hdim : Module.finrank (ZMod 2) E = 10)
    (eK : (K ⧸ pCore 2 K) ≃* SL5TenDimensional.Group)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH τ eK) : sourceOne L T V₁ ≤ K :=
  source_component_containment_of_model_residual d hH h hU hV hne g hsquare hout σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ τ hτ eK hs c
    (BinaryLinearNormalizerResidual.ten_dimensional_residual_le τ (MulEquiv.refl _) hdim)

/-- Retain the given degree-one field marking while proving containment. -/
theorem source_degree_one_natural_containment (F : BinaryField) (hF : F.degree = 1)
    (n : ℕ)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) F.Carrier)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearNatural F n) eK) :
    sourceOne L T V₁ ≤ K := by
  let E := ExtensionConsequences.degreeOneNaturalEquiv F hF n
  have hf : Function.Injective (linearNatural F n) := by
    intro a b hab
    apply E.groupEquiv.injective
    apply specialLinearNatural_injective n
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := E.linearEquiv.surjective v
    exact (E.intertwines a w).symm.trans ((congrArg (fun f => E.linearEquiv (f w)) hab).trans
      (E.intertwines b w))
  have hm : (pResidual 2 (linearNormalizer (linearNatural F n))).map
      (linearNormalizer (linearNatural F n)).subtype ≤ actionImage (linearNatural F n) :=
    BinaryNormalizerResidual.residual_le_of_equiv _ (specialLinearNatural n)
      E.groupEquiv E.linearEquiv E.intertwines
      (BinaryLinearNormalizerResidual.natural_residual_le n)
  exact source_component_containment_of_model_residual d hH h hU hV hne g hsquare hout σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ
    (linearNatural F n) hf eK hs c hm

/-- The original ordinary source excludes a binary natural degree-four component. -/
theorem source_binary_four_false
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (specialLinearNatural 4) eK) : False := by
  have hL₁K := source_binary_natural_containment d hH h hU hV hne g hsquare hout σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ c 4 eK hs
  exact linear_four_false d eL h1221 hH h hm hKH hKC hL₁K ρ hρ eK hs

/-- The original ordinary source excludes a binary natural degree-five component. -/
theorem source_binary_five_false
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (_h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (specialLinearNatural 5) eK) : False := by
  have hL₁K := source_binary_natural_containment d hH h hU hV hne g hsquare hout σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ c 5 eK hs
  exact linear_five_false d eL hH hm hKH hL₁K ρ hρ eK hs

/-- The ten-dimensional row is excluded without assuming point-residual containment. -/
theorem source_binary_ten_false
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (_h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) SL5TenDimensional.Group E) [IsIrreducible τ]
    (hτ : Function.Injective τ) (hdim : Module.finrank (ZMod 2) E = 10)
    (eK : (K ⧸ pCore 2 K) ≃* SL5TenDimensional.Group)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH τ eK) : False := by
  have hL₁K := source_binary_ten_containment d hH h hU hV hne g hsquare hout σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ c τ hτ hdim eK hs
  exact ten_dimensional_false d eL hH hm hKH hL₁K ρ hρ τ hdim eK hs
end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
