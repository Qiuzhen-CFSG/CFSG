module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SL2FourChiefUpper
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.Extensions
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors

/-!
# The literal selected SL₂(4) chief-count consumer

The component model is given on K/O₂(K). Its standard star equivalence transports
this marking to the actual component inside H/O₂(H), and the five-line action
identifies determinant-one matrices over the field of four elements with A₅.
Consequently five noncentral chief factors contradict the original actor bound.
The independent rank-four source lower bound supplies the five-factor premise.
Source: Aschbacher–Smith, 13.7.13, printed p.943.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The actual SL₂(4) component marking discharges the model identification in
the five-chief-factor contradiction. -/
theorem source_sl2Four_false_of_five_chief_factors
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
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
    (hKH : K ≤ H) (hKC : (K.subgroupOf H).IsCComponent)
    (hK : IsComponent (H ⧸ pCore 2 H) (Section08.Source.starImage H K))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (eK : (K ⧸ pCore 2 K) ≃* Representation.SL2FourNatural.SL)
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (t : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁)
    (h0 : t.head = ⊥) (h1 : t.last = ⊤) (hfive : 5 ≤ t.noncentralTwoCount) : False := by
  exact source_five_false_of_five_chief_factors d h hU hV hne g hs hout
    σ s B hB hBA (K.subgroupOf H) hKC hK hk hcomm
    ((componentModelEquiv hKH hKC eK).trans SL2FourNatural.alternatingFiveEquiv)
    hspan t h0 h1 hfive

end CFSG.Quasithin.Chapter13.Section07
