module
public import CFSG.Quasithin.Chapter13.Section07.ComponentPlaneSource
public import CFSG.Quasithin.Chapter13.Section07.ComponentSeedMarked

/-!
# The marked B.5 seed for the original plus action

The genuine source plane bound on UH/U₀, faithful quotient action and
selected component construct the prepared offender-restricted seed and
retain the complete marked B.5 conclusion. This is the source application
of the marked-seed producer; it assumes no plane bound on UH/V₁.

Source: Aschbacher–Smith,13.7.15–13.7.18, printed pp.943–945.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ComponentReduction
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
theorem source_plus_component_marked_seed
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
    (K : Subgroup H) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H))) :
    let J := K.map (QuotientGroup.mk' (pCore 2 H))
    let N := offenderSubgroup σ
    ∃ (_hJN : J ≤ N) (_hBN : B ≤ N),
      ∃ hcommN : ⁅J.subgroupOf N,B.subgroupOf N⁆ = J.subgroupOf N,
        ∃ _p : Prepared (σ.comp N.subtype) KnownSimple.IsKnownSimple hcommN,
          Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (seedQuotientAction (σ.comp N.subtype) hcommN)
            (seedComponentImage (σ.comp N.subtype) hcommN)) ∧
          naturalSeedSpace (σ.comp N.subtype) (J.subgroupOf N) (B.subgroupOf N) =
            moved (σ.comp N.subtype) (J.subgroupOf N) ∧
          moved (seedQuotientAction (σ.comp N.subtype) hcommN)
            (seedComponentImage (σ.comp N.subtype) hcommN) = ⊤ := by
  have hp := source_plus_seed_plane d h hU hV hne g hs hout σ s B hBA
  exact ChapterB.SourceInduction.component_marked_seed_of_minimal_plane σ
    (source_plus_faithful_of_kernel_eq σ s hk) (pCore_quotient_pCore_eq_bot 2)
    (source_plus_sqtk_cover d h) hK hB hcomm
    ((Submodule.finrank_mono hp.2).trans_eq hp.1)

end CFSG.Quasithin.Chapter13.Section07
