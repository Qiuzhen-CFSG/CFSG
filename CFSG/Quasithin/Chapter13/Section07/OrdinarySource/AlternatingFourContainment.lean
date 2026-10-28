module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.ComponentContainment
public import Theory.Representation.BinaryNormalizerResidual
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer

/-!
# Original containment of the four-dimensional alternating-seven component

The actual raw moved section extends to a faithful ambient action on the
supplied four-dimensional A₇ module. Every faithful A₇ image in GL₄(2) is
self-normalizing; its two-residual therefore has no image outside A₇.
The original point residual is two-perfect and lifts through the two-core.

This retains the arbitrary faithful four-dimensional action and its exact
component quotient marking. No deleted permutation action is inferred.
Source: Aschbacher--Smith,13.7.6(4), printed pp.939--940.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.Source Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.ModelExtension
open ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The actual dimension-four A₇ row contains the original point residual. -/
theorem source_alternating_seven_four_containment
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
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) E)
    (hτ : Function.Injective τ) (hdim : Module.finrank (ZMod 2) E = 4)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH τ eK)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H)))) : sourceOne L T V₁ ≤ K := by
  let : FiniteDimensional (ZMod 2) E := Module.finite_of_finrank_pos (by omega)
  exact source_component_containment_of_model_residual d hH h hU hV hne g hsquare hout
    σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ τ hτ eK hs c
    (BinaryNormalizerResidual.residual_le_of_normalizer_eq τ
      (BinaryAlternatingSevenControl.actionImage_self_normalizing τ hτ hdim))

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
