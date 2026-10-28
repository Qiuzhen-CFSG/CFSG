module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.ChiefImages
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Normalization
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.Representation.PerfectInvolutionExtension
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Source.Module

/-!
# The actual chief images in the source A₅ component argument

The component and the distinguished involution generate K*V*. Its noncentral
irreducible chief sections restrict irreducibly to the component, because
the involution moves at most two dimensions. The literal component image is
quasisimple and a section of the original SQTK group. The proved Theorem A
supplies its odd-prime rank bounds, even if the chief kernel contains an odd
central subgroup. Its two-group quotient then supplies the full B.4 hypotheses.

Source: Aschbacher–Smith13.5.21, printed p.924, the original applications of
B.4.2 and B.4.5. No component-model shortlist or kernel-order premise is used.
-/
public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Section08.Source Configuration
open ChapterB.QuasisimpleSource.IrreducibleBranch
open ChapterB.ComponentRecognition.SQTKSectionImage
universe u
/-- Genuine B.4 hypotheses for a component generated with a small-displacement actor. -/
theorem source_b4_hypotheses_of_component
    {E W : Type u} [Group E] [Finite E] [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) E W)
    (L : Subgroup E) [L.Normal] [IsQuasisimple L]
    (hρ : IsIrreducible ρ)
    (hE : IsSQTK KnownSimple.IsKnownSimple E)
    (hquot : IsPGroup 2 (E ⧸ L))
    (hcomponent : ¬ L ≤ ρ.ker)
    (v : E) (hgen : L ⊔ zpowers v = ⊤)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ v - 1)) ≤ 2) :
    Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.B4Hypotheses
      KnownSimple.IsKnownSimple (imageRepresentation ρ) := by
  have hirr := PerfectInvolutionExtension.restriction_irreducible ρ hρ L hcomponent v hgen hr
  let M : Subgroup (actionImage ρ) := actionSubgroup ρ L
  let f := actionHom ρ
  have hf : Function.Surjective f := ρ.asGroupHom.rangeRestrict_surjective
  let : M.Normal := Subgroup.Normal.map inferInstance f hf
  have hmap : L ≤ M.comap f := fun _ hl => mem_map_of_mem f hl
  have hqM : IsPGroup 2 (actionImage ρ ⧸ M) :=
    hquot.of_surjective (QuotientGroup.map L M f hmap)
      (QuotientGroup.map_surjective_of_surjective L M f
        ((QuotientGroup.mk'_surjective M).comp hf) hmap)
  have hMbot : M ≠ ⊥ := by
    intro hbot
    apply hcomponent
    have hmapbot : L ≤ (actionHom ρ).ker :=
      (Subgroup.map_eq_bot_iff L).mp hbot
    simpa [action_kernel_eq ρ] using hmapbot
  let : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMbot
  let : IsQuasisimple M := IsQuasisimple.of_surjective
    (f.subgroupMap L) (f.subgroupMap_surjective L)
  have hsem : ChapterA.Section02.IsSemisimple M := by
    apply top_unique
    exact le_sSup (show IsComponent M ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hsec : ChapterA.Section02.IsSectionOf M E :=
    ⟨L,f.subgroupMap L,f.subgroupMap_surjective L⟩
  have hM : IsSQTK KnownSimple.IsKnownSimple M :=
    ⟨ChapterA.Section02.theoremA_knownSimple.stronglyQuasithin_section
      hE.stronglyQuasithin hE.isKGroup hsec hsem,hsec.isKGroup hE.isKGroup⟩
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple (actionImage ρ) :=
    sqtk_of_twoGroup_quotient knownSimple_containsSimpleTwoGroups M hqM hM
  have hcore : pCore 2 (actionImage ρ) = ⊥ := by
    let _ : IsIrreducible (imageRepresentation ρ) :=
      imageRepresentation_irreducible ρ hρ
    exact actionImage_twoCore_eq_bot ρ hρ
  have hfit : generalizedFitting (actionImage ρ) = M :=
    generalizedFitting_eq_of_quasisimple_two_quotient M hqM hcore
  have hirrM : IsIrreducible ((imageRepresentation ρ).comp M.subtype) := by
    change IsIrreducible
      ((imageRepresentation ρ).comp (actionSubgroup ρ L).subtype)
    let fL : L →* actionSubgroup ρ L := (actionHom ρ).subgroupMap L
    apply (irreducible_comp_surjective_iff fL
      (f.subgroupMap_surjective L)
      ((imageRepresentation ρ).comp (actionSubgroup ρ L).subtype)).mp
    have heq :
        ((imageRepresentation ρ).comp (actionSubgroup ρ L).subtype).comp fL =
          ρ.comp L.subtype := by
      ext x w
      rfl
    rw [heq]
    exact hirr
  have hfitqs : IsQuasisimple (generalizedFitting (actionImage ρ)) := by
    rw [hfit]
    infer_instance
  have hfitirr : IsIrreducible
      ((imageRepresentation ρ).comp (generalizedFitting (actionImage ρ)).subtype) := by
    rw [hfit]
    exact hirrM
  exact ⟨hsqtk, imageRepresentation_injective ρ, hfitqs, hfitirr⟩

variable {G : Type u} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The full B.4 hypotheses on every original noncentral irreducible chief section. -/
@[expose] def ChiefHypotheses : Prop :=
  ∀ U N : Subrepresentation (representation D K h),
    ¬ component D K ≤ (chiefRepresentation D K h U N).ker →
    IsIrreducible (chiefRepresentation D K h U N) →
    Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.B4Hypotheses
      KnownSimple.IsKnownSimple (imageRepresentation (chiefRepresentation D K h U N))

omit [Finite G] [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- The original marked involution and component generate their literal actor. -/
theorem source_actor_generation (v : actor D K)
    (hv : zpowers (v : Hstar D.H) = starImage D.H D.V) :
    component D K ⊔ zpowers v = ⊤ := by
  apply map_injective (actor D K).subtype_injective
  rw [Subgroup.map_sup,component,map_subgroupOf_eq_of_le
    (show starImage D.H K ≤ actor D K from le_sup_left),MonoidHom.map_zpowers,
    Subgroup.subtype_apply,hv,← MonoidHom.range_eq_map,range_subtype]
  rfl

/-- Every original noncentral chief action satisfies B.4.2 and B.4.5's hypotheses. -/
theorem source_chief_hypotheses (s : Selected D K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) = 2)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hirr : IsIrreducible (chiefRepresentation D K h U N)) :
    Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.B4Hypotheses
      KnownSimple.IsKnownSimple (imageRepresentation (chiefRepresentation D K h U N)) := by
  have hc := LocalGeometry.star_V_card_two h hi hu
  have hnorm := (s.normalizes_and_commutator h hc (selected_section_even s)).1
  let : (component D K).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (starImage D.H K).le_normalizer hnorm)
  let : IsQuasisimple (starImage D.H K) := s.quasisimple
  let : IsQuasisimple (component D K) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe
      (show starImage D.H K ≤ actor D K from le_sup_left)).symm
  have hp : IsPGroup 2 (zpowers v) := by
    have he := Nat.card_congr (Subgroup.equivMapOfInjective (zpowers v)
      (actor D K).subtype (actor D K).subtype_injective).toEquiv
    rw [MonoidHom.map_zpowers] at he
    change Nat.card (zpowers v) = Nat.card (zpowers (v : Hstar D.H)) at he
    rw [hv] at he
    exact IsPGroup.of_card (n := 1) (he.trans hc)
  have hq : IsPGroup 2 (actor D K ⧸ component D K) :=
    isPGroup_quotient_of_sup_eq_top _ _ hp (source_actor_generation D K v hv)
  have hr' := fixedCodim_section_le (representation D K h) U N (zpowers v)
  rw [fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at hr'
  exact source_b4_hypotheses_of_component (chiefRepresentation D K h U N)
    (component D K) hirr
    ((Chapter1.Section02.uniqueness_local_quotient_sqtk hG hH).subgroup (actor D K))
    hq hn v (source_actor_generation D K v hv) (hr'.trans hr.le)

/-- All genuine chief-action hypotheses, with the marked involution constructed internally. -/
theorem source_chief_hypotheses_all (s : Selected D K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16) : ChiefHypotheses D K h := by
  have hc := LocalGeometry.star_V_card_two h hi hu
  have hcyc : IsCyclic (starImage D.H D.V) := isCyclic_of_prime_card hc
  obtain ⟨x,hx⟩ := (starImage D.H D.V).isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hxV : x ∈ starImage D.H D.V := hx ▸ mem_zpowers x
  let v : actor D K := ⟨x,(show starImage D.H D.V ≤ actor D K from le_sup_right) hxV⟩
  have hv : zpowers (v : Hstar D.H) = starImage D.H D.V := hx
  have hr : Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) = 2 := by
    change Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - LinearMap.id)) = 2
    rw [← fixedCodim_zpowers_eq_displacement_rank,hv,sourceRepresentation_eq h]
    exact Fitting.SourceAction.source_fixedCodim_two h hi hu hcard
  intro U N hn hirr
  exact source_chief_hypotheses D K h s hG hH hi hu v hv hr U N hn hirr

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
