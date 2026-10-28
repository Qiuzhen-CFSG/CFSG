module

public import CFSG.Quasithin.Chapter13.Section07.SmallMovedCatalogue
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Complete

/-!
# The complete original 13.7.15(1–2) model sieve

The original seed-plane geometry and corrected B.5.1 row on K*B* imply both
Irr⁺ on the original moved subspace and the four concrete actor families.
The last covered-A6 row is eliminated on its actual faithful central quotient.
The construction of the B.5.1 row from the selected faithful action image is
retained with the earlier-source assembly owner.

Source: Aschbacher–Smith 13.7.15(1–2), printed pp.943–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- All source model alternatives are discharged on the original selected component. -/
theorem source_plus_component_irrPlus_and_small_models
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
    (sK : MovedSection (σ.comp
      (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B).subtype)
      ((K.map (QuotientGroup.mk' (pCore 2 H))).subgroupOf
        (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B)))
    (hc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase (σ.comp
      (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B).subtype)
      ((K.map (QuotientGroup.mk' (pCore 2 H))).subgroupOf
        (K.map (QuotientGroup.mk' (pCore 2 H)) ⊔ B)) sK) :
    IsIrrPlus σ (K.map (QuotientGroup.mk' (pCore 2 H)))
      (moved σ (K.map (QuotientGroup.mk' (pCore 2 H)))) ∧ SmallMoved.ActorList (K.map (QuotientGroup.mk' (pCore 2 H))) := by
  obtain ⟨hi,hg⟩ := source_plus_component_small_models_or_triple
    d h hU hV hne g hs hout σ s B hB hBA K hK sK hc
  refine ⟨hi,?_⟩
  rcases hg with hg | ht
  · exact hg
  · obtain ⟨hf,hgen,⟨a⟩,C,_,hC,hdC⟩ := ht
    exact (SmallMoved.TripleSix.not_plane hf (hC.isOffender _)
      (hgen ▸ hC.le_offenderSubgroup _) hdC a).elim
end CFSG.Quasithin.Chapter13.Section07
