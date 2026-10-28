module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.ComponentModelAction
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.NoncontainedImages
public import Theory.Representation.BinaryOffender.MarkedNormalizerResidual

/-!
# Original point-residual containment from marked component models

The actual point residual remains two-perfect in H/O₂(H). Extend the
original raw component section to the faithful ambient model action, then
apply the model normalizer's two-residual bound. Its image containment
lifts through the actual two-core quotient because the component is normal.

The source theorem retains the original selected packet and the exact
model normalizer bound, to be discharged by the concrete binary families.
It does not assume point-residual containment or use13.7.19.
Source: Aschbacher--Smith,13.7.6, printed pp.938--940.
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

/-- Containment in the actual two-core quotient lifts to the point residual. -/
theorem source_point_residual_le_of_star_le
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    (hle : starImage H (sourceOne L T V₁) ≤ starImage H K) :
    sourceOne L T V₁ ≤ K := by
  by_contra hn
  exact source_noncontained_star_not_le hH hKH hKn hn hle

/-- The literal point residual stays two-perfect after taking its star image. -/
theorem source_local_star_twoPerfect
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M) :
    IsPPerfect 2 (starImage H (sourceOne L T V₁)) := by
  have hJH : sourceOne L T V₁ ≤ H := le_sup_left.trans hH.1.2
  let X := (sourceOne L T V₁).subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hp : IsPPerfect 2 X :=
    (isPPerfect_embedded_pResidual 2
      ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G))).of_surjective
      (subgroupOfEquivOfLe hJH).symm.toMonoidHom (subgroupOfEquivOfLe hJH).symm.surjective
  exact hp.of_surjective (q.subgroupMap X) (q.subgroupMap_surjective X)

/-- A faithful ambient model action bounds the literal point residual. -/
theorem source_component_containment_of_faithful_model_action
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hKC : (K.subgroupOf H).IsCComponent)
    (hKn : H ≤ normalizer (K : Set G))
    {D E : Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) D E)
    (eK : (K ⧸ pCore 2 K) ≃* D)
    (γ : Representation (ZMod 2) (Hstar H) E) (hγ : Function.Injective γ)
    (hres : ∀ (k : starImage H K) v,
      γ k v = τ (eK ((Section08.Components.componentStarEquiv H K hKH hKC).symm k)) v)
    (hmodel : (pResidual 2 (linearNormalizer τ)).map (linearNormalizer τ).subtype ≤
      actionImage τ) : sourceOne L T V₁ ≤ K := by
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := starImage H K
  let : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  let : J.Normal := (inferInstance : (K.subgroupOf H).Normal).map π (QuotientGroup.mk'_surjective _)
  apply source_point_residual_le_of_star_le hH hKH hKn
  exact le_normal_of_marked_normalizer_residual γ hγ J
    ((Section08.Components.componentStarEquiv H K hKH hKC).symm.trans eK) τ hres hmodel
    (starImage H (sourceOne L T V₁)) (source_local_star_twoPerfect hH)

/-- Apply the marked-model residual bound to the original selected source packet. -/
theorem source_component_containment_of_model_residual
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
    {D E : Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) D E) (hτ : Function.Injective τ)
    (eK : (K ⧸ pCore 2 K) ≃* D)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH τ eK)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hmodel : (pResidual 2 (linearNormalizer τ)).map (linearNormalizer τ).subtype ≤
      actionImage τ) : sourceOne L T V₁ ≤ K := by
  obtain ⟨γ,hγ,hres⟩ := source_component_model_action d h hU hV hne g hsquare hout
    σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ τ hτ eK hs c
  exact source_component_containment_of_faithful_model_action hH hKH hKC hKn
    τ eK γ hγ hres hmodel

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
