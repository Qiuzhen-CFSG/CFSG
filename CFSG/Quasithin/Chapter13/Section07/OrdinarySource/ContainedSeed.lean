module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.ContainedDispatch
public import CFSG.Quasithin.Chapter13.Section07.ComponentSeedRows
public import CFSG.Quasithin.Chapter13.Section07.ComponentCentralSection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.SubgroupSeed

/-!
# The actual contained prepared seed reaches the marked contradictions

Apply B.5 to the original plus offender, retain its literal reduced action,
and return that same action through the offender subgroup and the central
projection UH/V₁ → UH/U₀. An identity action equivalence suffices: concrete
row markings are composed only after obtaining the raw component model.
The original plane geometry also supplies noncentrality of VH/UH.

The remaining binary SL₃ and four-dimensional A₇ source exclusions are
explicit, separately owned inputs. This is their actual same-seed consumer.
Source: Aschbacher–Smith13.7.18–21, printed pp.945–946.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.TransvectionRecognition ChapterF.Section09.Setup
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.RecognitionStep
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ComponentReduction
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
universe u v
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
theorem source_contained_marked_seed_false
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
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hthree : ∀ e3 : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      HasSectionModel H V₃ V₁ ρ K hKH (specialLinearNatural 3) e3 → False)
    (hseven : ∀ (E : Type v) [AddCommGroup E] [Module (ZMod 2) E],
      ∀ τ7 : Representation (ZMod 2) (alternatingGroup (Fin 7)) E,
      Function.Injective τ7 → IsIrreducible τ7 → Module.finrank (ZMod 2) E = 4 →
      ∀ e7 : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7),
      HasSectionModel H V₃ V₁ ρ K hKH τ7 e7 → False)
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G)) : False := by
  have hU : IsMulCommutative (Section08.Source.UH H V₃) := inferInstance
  have hc := Section05.AmbientSource.source_parabolic_centralizer d eL h1221 hm
  have hb : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M := by
    rw [← d.first_normalizer]
    exact (Section05.PointAction.normalizer_intersection_source d hc).trans inf_le_left
  have hmove := source_noncentral_VH_quotient_of_earlier_geometry d h hU
    hH.2.1 hH.2.2 hb hne
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
  exact contained_marked_row_false d eL h1221 hm hH h hV hne g hsquare hout
    σ s B hB hBA hKH hK hKstar hk hcomm hL₁K ρ hρ c
    q.sectionData.action C hq.reduced_faithful _ hraw hq.reduced hthree (hseven _)
    hcentral hspan hmove

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
