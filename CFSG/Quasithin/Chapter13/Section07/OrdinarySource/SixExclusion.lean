module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SixChiefUpper
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SixChiefLower
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.LocalExclusion

/-!
# The selected natural A₆ component is impossible

On the original selected offender and component, the marked natural section
supplies at least six noncentral L₁-chief factors. The same paired conjugator
bounds the actual elementary actor by eight, giving at most five factors.
Constructing a complete chief series therefore gives a contradiction on the
literal point residual, with no chief-count assumption left to the caller.

Source: Aschbacher–Smith13.7.21, printed pp.945–946.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion Section08.TransvectionRecognition ChapterF.Section09.Setup
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The original selected natural A₆ component contradicts the two source chief counts. -/
theorem source_six_selected_false
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
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
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK)
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (hmove : ¬ ⁅Section08.Source.VH H V,H⁆ ≤ Section08.Source.UH H V₃) : False := by
  obtain ⟨t,h0,h1⟩ := exists_chiefSeries (⊥ : NormalNode (sourceOne L T V₁)) ⊤ bot_le
  have hl := source_six_chief_count_ge_six d hH h hKH hK hL₁K ρ hρ eK hs
    hcentral hmove t h0 h1
  have hu := source_six_chief_count_le_five d h inferInstance hV hne g hsquare hout
    σ s B hB hBA (K.subgroupOf H) hK hKstar hk hcomm
    (componentModelEquiv hKH hK eK) hspan
  rw [PlusAction.source_local_residual_eq d h] at hu
  have hb := hu t h0 h1
  omega

end CFSG.Quasithin.Chapter13.Section07
