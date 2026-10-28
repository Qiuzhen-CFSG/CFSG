module
public import CFSG.Quasithin.Chapter13.Section07.ComponentSeedSource
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Marked

/-!
# Marked small-plane rows on the original plus component seed

The original source plane bound descends through the actual offender
restriction and prepared seed quotient. Inspecting the full B.5 conclusion
then retains each surviving action marking on that literal section.

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
theorem source_plus_component_marked_rows
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
          ∃ q : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (seedQuotientAction (σ.comp N.subtype) hcommN)
            (seedComponentImage (σ.comp N.subtype) hcommN),
          naturalSeedSpace (σ.comp N.subtype) (J.subgroupOf N) (B.subgroupOf N) =
            moved (σ.comp N.subtype) (J.subgroupOf N) ∧
          moved (seedQuotientAction (σ.comp N.subtype) hcommN)
            (seedComponentImage (σ.comp N.subtype) hcommN) = ⊤ ∧
          ChapterB.QuasisimpleSource.SmallMoved.SectionPlaneCase
            (seedQuotientAction (σ.comp N.subtype) hcommN) q.sectionData := by
  have hseed :=
    source_plus_component_marked_seed d h hU hV hne g hs hout σ s B hB hBA K hK hk hcomm
  dsimp only at hseed
  obtain ⟨hJN,hBN,hcommN,p,hq,he,hm⟩ := hseed
  obtain ⟨q⟩ := hq
  have hp := source_plus_seed_plane d h hU hV hne g hs hout σ s B hBA
  have hd : Module.finrank (ZMod 2) (moved σ B) ≤ 2 :=
    (Submodule.finrank_mono hp.2).trans_eq hp.1
  have hdN : Module.finrank (ZMod 2)
      (moved (σ.comp (offenderSubgroup σ).subtype) (B.subgroupOf (offenderSubgroup σ))) ≤ 2 := by
    change Module.finrank (ZMod 2) (subspaceCommutator
      (σ.comp (offenderSubgroup σ).subtype) ⊤ (B.subgroupOf (offenderSubgroup σ))) ≤ 2
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBN]
    exact hd
  exact ⟨hJN,hBN,hcommN,p,q,he,hm,
    ChapterB.QuasisimpleSource.SmallMoved.source_marked_of_plane _
      (p.minimal.1.isOffender _)
      (ChapterB.SourceInduction.seedOffender_moved_le _ hcommN hdN)
      q.sectionData q.clause_one⟩

end CFSG.Quasithin.Chapter13.Section07
