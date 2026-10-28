module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.NoncontainedNormalizer
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount

/-!
# Containment using the original block chief bound

The noncontained natural SL₂(4) component makes the actual local-core
normalizer escape M. An alternating A₆ block would force at most two
noncentral chief factors in L₁, contradicting the original full-span
lower bound. Only the earlier normalizer-escape-to-block source input
remains in this containment theorem.

Source: Aschbacher–Smith 13.7.19, printed p.945.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion ChapterF.Section09.Setup
open Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

theorem source_sl2Four_containment_of_block
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
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
    (eK : (K ⧸ pCore 2 K) ≃* Representation.SL2FourNatural.SL)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (SL2OrthogonalCover.binaryNatural (F := SL2FourNatural.F)) eK)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hblock : (¬ H ⊓ normalizer
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ M) →
      ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6) :
    sourceOne L T V₁ ≤ K := by
  by_contra hnot
  obtain ⟨e,he,hr,hes⟩ := source_noncontained_semilinear_and_escape d h1221 hH h hU hV
    hne g hsquare hout σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ eK hs c hnot
  exact source_not_alternatingBlock d h hU hV (hblock hes)


end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
