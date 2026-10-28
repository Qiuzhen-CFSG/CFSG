module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NaturalRows
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentStructure
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.BinaryComponentMarking
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.NaturalEndpoints
public import CFSG.Quasithin.Chapter13.Section05.A5Source.CentralQuotient

/-!
# The complete original A₅ chief catalogue

The source configuration proves that the selected star component is simple,
contains L₁, and is normal in H. The original moved plane and full component
generation make every maximal quotient faithful. The complete chief sieve
and its source exclusions supply the three natural component restrictions.
Their actual ambient extensions give S₆, A₈, or G₂(2)′, with the original
component marking and equivariant module coordinates.

The final theorem applies this catalogue to the original central-quotient
consumer. Relative normality, ambient core generation, the faithful natural
quotient, and its embedded rank-two seed have no remaining recognition premise.
Source: Aschbacher–Smith13.5.21, printed pp.923–924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section08
open ComponentReduction Section08.Source Recognition
open CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Catalogue ChapterB.QuasisimpleSource MarkedModule.CentralQuotient

private theorem top_section_natural {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W)
    (L : Subgroup E) (N : Subrepresentation ρ)
    (hnat : NaturalAction L (sectionRepresentation ρ N ⊤)) :
    NaturalAction L N.quotientRepresentation := by
  let q := topSectionEquiv ρ N
  have hi (g : E) (w) : q.symm (N.quotientRepresentation g w) =
      sectionRepresentation ρ N ⊤ g (q.symm w) := by
    apply q.injective
    rw [q.apply_symm_apply,topSectionEquiv_intertwines,q.apply_symm_apply]
  rcases hnat with hs | hs | hs
  · obtain ⟨e,f,hL,hf⟩ := hs
    refine Or.inl ⟨e,q.symm.trans f,hL,?_⟩
    intro g w
    exact (congrArg f (hi g w)).trans (hf g (q.symm w))
  · obtain ⟨e,f,hL,hf⟩ := hs
    refine Or.inr (Or.inl ⟨e,q.symm.trans f,hL,?_⟩)
    intro g w
    exact (congrArg f (hi g w)).trans (hf g (q.symm w))
  · obtain ⟨e,f,hL,hf⟩ := hs
    refine Or.inr (Or.inr ⟨e,q.symm.trans f,hL,?_⟩)
    intro g w
    exact (congrArg f (hi g w)).trans (hf g (q.symm w))

universe u
variable {G : Type u} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : D.H ∈ Hz D.L₁ (D.T : Subgroup G)
    (centralizer (D.V₁ : Set G)) (normalizer (D.L : Set G)))
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h hA312 hH

/-- The actual A₅ source has the complete natural chief catalogue,
with every group, faithfulness, and module-coordinate premise discharged. -/
theorem source_chief_catalogue (hU : ¬ IsMulCommutative D.UH)
    (K : Subgroup G) (s : Selected D K) [(componentCentralizer s h).Normal]
    (c : SourceConfiguration s h D.L₁ le_rfl) :
    ChiefCatalogue D h K := by
  have hsimple := Catalogue.source_component_simple D K h s d.hypothesis.qtke hH.1.1
    d.third_index hU d.module_card c
  obtain ⟨hLK,hnK⟩ := Catalogue.source_local_le_component D K h s d.hypothesis.qtke hH.1.1
    d.third_index hU d.module_card c (residual_quotient_card d hA312 hH hU)
  let : IsSimpleGroup (starImage D.H K) := hsimple
  let : (starImage D.H K).Normal := Subgroup.Normal.map hnK _ (QuotientGroup.mk'_surjective _)
  let : (component D K).Normal := by
    change ((starImage D.H K).subgroupOf (actor D K)).Normal
    infer_instance
  intro N hN hn
  obtain ⟨rows,hcentral⟩ := source_natural_component_rows d h hU K s c hLK hnK N hN hn
  obtain ⟨v,hv,_,P,hP⟩ := source_actor_marking d h hU K s
  apply top_section_natural _ (component D K) N
  rcases rows with ha | ha | ha <;> obtain ⟨a⟩ := ha
  · exact NaturalEndpoints.alternating_six _ (component D K)
      (top_section_faithful _ N (source_head_faithful d h hU K s hLK hnK N hN))
      (source_six_component_ne_top s h c a.groupEquiv) a
  · exact NaturalEndpoints.alternating_eight _ (component D K) hcentral a P v hP
      (source_actor_generation D K v hv)
  · exact NaturalEndpoints.g2_two _ (component D K) hcentral a P v hP
      (source_actor_generation D K v hv)

variable
  (h17 : ∀ J ∈ Hz D.L₁ (D.T : Subgroup G)
    (centralizer (D.V₁ : Set G)) (normalizer (D.L : Set G)),
    ¬ IsMulCommutative (UH J D.Vplus) → (D.L₁.subgroupOf J).Normal →
      ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
  (hnot : ¬ ModelConclusion G 5)
include h17 hnot

/-- Apply the proved original chief catalogue to the literal central-quotient
consumer, removing its independent recognition assumptions. -/
theorem source_central_quotient_of_configuration (hU : ¬IsMulCommutative D.UH)
    (K : Subgroup G) (s : Selected D K) [(componentCentralizer s h).Normal]
    (c : SourceConfiguration s h D.L₁ le_rfl) :
    (K.subgroupOf D.H).Normal ∧ D.UH = ⁅D.QH,K⁆ ∧
    ∃ hn : (starImage D.H K).Normal,
      D.tilde D.UH = ⁅D.tilde D.UH,D.tilde K⁆ ∧
      subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤ ∧
      NaturalAction (Catalogue.component D K)
        ((MarkedModule.CentralQuotient.representation D h K hn).comp (Catalogue.actor D K).subtype) ∧
      Function.Injective (MarkedModule.CentralQuotient.representation D h K hn) ∧
      Function.Injective (MarkedModule.CentralQuotient.seedMap D h K) ∧
      Module.finrank (ZMod 2) (MarkedModule.CentralQuotient.seedSpace D h K) = 2 := by
  have hsimple := Catalogue.source_component_simple D K h s d.hypothesis.qtke hH.1.1
    d.third_index hU d.module_card c
  obtain ⟨hLK,_⟩ := Catalogue.source_local_le_component D K h s d.hypothesis.qtke hH.1.1
    d.third_index hU d.module_card c (residual_quotient_card d hA312 hH hU)
  let : IsSimpleGroup (starImage D.H K) := hsimple
  exact source_central_quotient d h hA312 hH h17 hnot hU K s hLK
    (source_chief_catalogue d h hA312 hH hU K s c)

end CFSG.Quasithin.Chapter13.Section05.A5Source
