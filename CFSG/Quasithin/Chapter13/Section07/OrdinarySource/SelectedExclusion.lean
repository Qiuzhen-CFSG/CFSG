module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SelectedContainment
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeExclusion

/-!
# The selected original component contradiction

Retain the genuine B.5 action marking through the plus-to-raw central
projection. The original marked rows give point-residual containment;
all surviving rows except binary SL₃ are excluded by their source
geometry and chief counts. The literal C₃-system contradiction excludes
that final binary SL₃ row. Component normality is supplied by13.7.15.

The earlier kernel equality, fixed-layer centrality, plane noncentrality
and normalizer-escape-to-block input remain explicit. No model-recognition
or final row-exclusion callback remains.
Source: Aschbacher–Smith 13.7.18–21, printed pp.945–946.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.TransvectionRecognition ChapterF.Section09.Setup
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component
open ChapterB.QuasisimpleSource
universe v
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
theorem source_selected_component_false_of_block
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hsquare : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKstar : IsComponent (H ⧸ pCore 2 H) (Section08.Source.starImage H K))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (hblock : (¬ H ⊓ normalizer
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ M) →
      ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6) : False := by
  have hU : IsMulCommutative (Section08.Source.UH H V₃) := inferInstance
  have hn := source_plus_component_normal d h hU hV hne g hsquare hout
    σ s B hB hBA (K.subgroupOf H) hK hKstar hk hcomm
  have hKn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hn
  have hL₁K := source_marked_seed_containment d h1221 hH h hV hne g hsquare hout
    σ s B hB hBA hKH hK hKstar hKn hk hcomm ρ hρ c hcentral hblock
  obtain ⟨e3,hs3⟩ := source_contained_component_linear_three d eL h1221 hm hH h hV hne
    g hsquare hout σ s B hB hBA hKH hK hKstar hk hcomm hL₁K ρ hρ c hcentral hspan
  exact linear_three_false d hH h hU hV hm hKH hK hL₁K ρ hρ e3 hs3

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
