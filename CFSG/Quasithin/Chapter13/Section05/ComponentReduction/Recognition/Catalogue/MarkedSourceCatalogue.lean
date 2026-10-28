module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.MarkedClassification
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.SourceChiefMarked
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Full classification of the original marked chief actions in 13.5.21

The actual marked involution survives each noncentral chief section and moves
at most two binary dimensions. Its cyclic group supplies the quadratic bound,
so the complete marked source classifier applies to the faithful action image.
All SQTK, faithfulness, quasisimplicity, irreducibility and marked-involution
hypotheses are constructed by the original source configuration. The full
B.4.2 and fourteen-row B.4.5 action alternatives remain unchanged.

Source: Aschbacher–Smith 13.5.21, printed pp.923–924 (PDF pp.940–941).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open ChapterB.SmallRatioClassification
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) G V}

theorem fullCatalogue_of_marked_involution
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) : FullCatalogueAction ρ := by
  have hq : quadraticRatio ρ ≤ 2 := by
    obtain ⟨hA,hrank,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ t ht
    apply (quadraticRatio_le_two_iff ρ).mpr
    refine ⟨zpowers t,hA,hquad,?_⟩
    rw [hrank,fixedCodim_zpowers_eq_displacement_rank]
    exact hr
  exact actionCase_of_small_involution (rankOne_source_of_b4_quadratic h hq) hq t ht hr


section SourceChief
open Section08.Source CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
variable {E : Type u} [Group E] [Finite E]
  (D : ChapterF.Section09.Setup E) (K : Subgroup E) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- Apply the full catalogue to each literal noncentral irreducible chief image. -/
theorem source_chief_fullCatalogue (s : Selected D K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple E) (hH : D.H ∈ Chapter1.H E)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hirr : IsIrreducible (chiefRepresentation D K h U N)) :
    FullCatalogueAction (imageRepresentation (chiefRepresentation D K h U N)) := by
  have hyp := source_chief_hypotheses_all D K h s hG hH hi hu hcard U N hn hirr
  obtain ⟨t,ht,hr,_⟩ := source_chief_marked_all D K h s hG hH hi hu hcard U N hn hirr
  exact fullCatalogue_of_marked_involution hyp t ht hr
end SourceChief
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
