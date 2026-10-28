module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.ContainedClassification
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BinaryLinearContainment
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.FourFieldContainment
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.NoncontainedBlock
public import Theory.Representation.BinaryNormalizerResidual.AlternatingModels

/-!
# Containment of the original marked component

The actual B.5 marked rows retain the raw component-section equivalence.
Their linear-normalizer residual bounds put the original point residual
inside the component. The natural SL₂(4) row uses the marked semilinear
normalizer and the already-proved block chief bound; it retains only the
genuine earlier escape-to-block source input.

The same prepared offender supplies this containment without a separate
model mark, and the final consumer leaves the binary natural SL₃(2) row.
Source: Aschbacher–Smith 13.7.6, 13.7.18–19, printed pp.938–940,945.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.TransvectionRecognition ChapterF.Section09.Setup
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.RecognitionStep
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
theorem source_marked_row_containment
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hsquare : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
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
    (hKn : H ≤ normalizer (K : Set G))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) A E) (J : Subgroup A)
    [IsIrreducible (τ.comp J.subtype)]
    (hf : Function.Injective (τ.comp J.subtype))
    (eK : (K ⧸ pCore 2 K) ≃* J)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (τ.comp J.subtype) eK)
    (hrows : SmallMoved.PlaneActionCase τ J)
    (hblock : (¬ H ⊓ normalizer
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ M) →
      ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6) :
    sourceOne L T V₁ ≤ K := by
  let : IsQuasisimple (Section08.Source.starImage H K) := hKstar.2
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (Section08.Components.componentStarEquiv H K hKH hK).symm
  let : IsQuasisimple J := IsQuasisimple.of_mulEquiv eK
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
  have hU : IsMulCommutative (Section08.Source.UH H V₃) := inferInstance
  have hc : (pResidual 2 (linearNormalizer (τ.comp J.subtype))).map
      (linearNormalizer (τ.comp J.subtype)).subtype ≤ actionImage (τ.comp J.subtype) →
      sourceOne L T V₁ ≤ K :=
    source_component_containment_of_model_residual d hH h hU hV hne g hsquare hout
      σ s B hB hBA hKH hK hKstar hKn hk hcomm ρ hρ (τ.comp J.subtype) hf eK hs c
  cases hrows with
  | linearTwo F hF em =>
    let em' := SmallMoved.linearTwoFourActionEquiv F hF em
    exact source_sl2Four_containment_of_block d h1221 hH h hU hV hne g hsquare hout
      σ s B hB hBA hKH hK hKstar hKn hk hcomm ρ hρ (eK.trans em'.groupEquiv)
      (hs.actionEquiv em') c hblock
  | linearThree F hF em =>
    by_cases hF2 : F.degree = 2
    · exact source_linear_three_four_containment d hH h hU hV hne g hsquare hout
        σ s B hB hBA hKH hK hKstar hKn hk hcomm ρ hρ F hF2
        (eK.trans em.groupEquiv) (hs.actionEquiv em) c
    · have hF1 : F.degree = 1 := by have := F.degree_pos; omega
      let em' := SmallMoved.linearThreeTwoActionEquiv F hF1 em
      exact source_binary_natural_containment d hH h hU hV hne g hsquare hout
        σ s B hB hBA hKH hK hKstar hKn hk hcomm ρ hρ c 3
        (eK.trans em'.groupEquiv) (hs.actionEquiv em')
  | symplectic F hF em =>
    exact source_symplectic_four_four_containment d hH h hU hV hne g hsquare hout
      σ s B hB hBA hKH hK hKstar hKn hk hcomm ρ hρ F hF
      (eK.trans em.groupEquiv) (hs.actionEquiv em) c
  | symplecticTwo em =>
    let em' := ExtensionConsequences.SymplecticTwo.markedAlternatingActionEquiv em
    apply hc
    exact BinaryNormalizerResidual.residual_le_of_equiv _ _ em'.groupEquiv
      em'.linearEquiv em'.intertwines
      (BinaryNormalizerResidual.alternating_small_natural_residual_le 6 (by omega))
  | symmetric n hn em =>
    let em' := ExtensionConsequences.markedRestriction em
    apply hc
    exact BinaryNormalizerResidual.residual_le_of_equiv _ _ em'.groupEquiv
      em'.linearEquiv em'.intertwines
      (BinaryNormalizerResidual.alternating_small_natural_residual_le n (by omega))
  | alternatingSix em =>
    apply hc
    exact BinaryNormalizerResidual.residual_le_of_equiv _ _ em.groupEquiv
      em.linearEquiv em.intertwines
      (BinaryNormalizerResidual.alternating_small_natural_residual_le 6 (by omega))
  | alternatingSeven eg hd =>
    let : FiniteDimensional (ZMod 2) E := Module.finite_of_finrank_pos (by omega)
    exact hc (BinaryNormalizerResidual.alternatingSeven_four_residual_le _ hf eg hd)
  | binaryLinear n hn em =>
    apply hc
    exact BinaryNormalizerResidual.residual_le_of_equiv _ _ em.groupEquiv
      em.linearEquiv em.intertwines (BinaryLinearNormalizerResidual.natural_residual_le n)
  | orthogonalSix em =>
    apply hc
    exact BinaryNormalizerResidual.residual_le_of_equiv _ _ em.groupEquiv
      em.linearEquiv em.intertwines
      (BinaryNormalizerResidual.alternating_small_natural_residual_le 8 (by omega))
  | symmetricEight em =>
    let em' := ExtensionConsequences.markedRestriction em
    apply hc
    exact BinaryNormalizerResidual.residual_le_of_equiv _ _ em'.groupEquiv
      em'.linearEquiv em'.intertwines
      (BinaryNormalizerResidual.alternating_small_natural_residual_le 8 (by omega))
  | exteriorFive eg hd =>
    exact hc (BinaryLinearNormalizerResidual.ten_dimensional_residual_le _ eg hd)

open ChapterB.SourceInduction.ComponentReduction
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
universe v

theorem source_marked_seed_containment
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
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
    (hKn : H ≤ normalizer (K : Set G))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hblock : (¬ H ⊓ normalizer
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ M) →
      ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6) :
    sourceOne L T V₁ ≤ K := by
  have hU : IsMulCommutative (Section08.Source.UH H V₃) := inferInstance
  let J := Section08.Source.starImage H K
  let N := offenderSubgroup σ
  have hp := source_plus_component_marked_rows d h hU hV hne g hsquare hout
    σ s B hB hBA (K.subgroupOf H) hKstar hk hcomm
  dsimp only at hp
  obtain ⟨hJN,hBN,hcommN,p,q,hseed,hmoved,hq⟩ := hp
  let C := seedComponentImage (σ.comp N.subtype) hcommN
  let τ := q.sectionData.action.comp C.subtype
  let em : ActionEquiv τ τ := ⟨MulEquiv.refl _,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  have hi := (source_plus_component_irrPlus_and_actor d h hU hV hne g hsquare hout
    σ s B hB hBA (K.subgroupOf H) hKstar hk hcomm).1
  have hplus := centralSectionModel_of_subgroup_seed_mark σ J N hJN hcommN p
    hKstar hi q.sectionData τ em
  have hraw := source_hasSectionModel_of_plus_model h K hKH hK hKstar ρ hρ c
    σ s hcentral τ _ hplus
  let : IsIrreducible τ := hq.reduced_irreducible
  exact source_marked_row_containment d h1221 hH h hV hne g hsquare hout
    σ s B hB hBA hKH hK hKstar hKn hk hcomm ρ hρ c
    q.sectionData.action C hq.reduced_faithful _ hraw hq.reduced hblock

theorem source_component_linear_three_of_block
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
    (hKn : H ≤ normalizer (K : Set G))
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
      ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6) :
    ∃ e3 : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      HasSectionModel H V₃ V₁ ρ K hKH (specialLinearNatural 3) e3 := by
  have hL₁K := source_marked_seed_containment d h1221 hH h hV hne g hsquare hout
    σ s B hB hBA hKH hK hKstar hKn hk hcomm ρ hρ c hcentral hblock
  exact source_contained_component_linear_three d eL h1221 hm hH h hV hne g hsquare hout
    σ s B hB hBA hKH hK hKstar hk hcomm hL₁K ρ hρ c hcentral hspan

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
