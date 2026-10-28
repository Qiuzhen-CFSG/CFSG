module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Head
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.FaithfulImages
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.NaturalRows
public import Theory.GroupAction.SylowPointwiseInner.Intrinsic
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner

/-!
# The natural component modules in the original A₅ source

Every maximal quotient is faithful by the original moved-plane argument.
Its actual component image is the simple generalized Fitting subgroup.
Pointwise Sylow fixation makes a binary-linear marked involution inner;
its transvection displacement contradicts the source irreducible plane.
The literal ten-dimensional section exclusion removes the exterior row.
The complete chief sieve then supplies the three natural restrictions,
retaining the original component coordinates and its trivial centralizer.
Source: Aschbacher–Smith13.5.21, printed p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open ComponentReduction Section08.Source Recognition
open CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Catalogue ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h

theorem source_natural_component_rows (hU : ¬ IsMulCommutative D.UH)
    (K : Subgroup G) (s : Selected D K) [(componentCentralizer s h).Normal]
    (c : SourceConfiguration s h D.L₁ le_rfl)
    (hLK : D.L₁ ≤ K) (hnK : (K.subgroupOf D.H).Normal)
    [IsSimpleGroup (starImage D.H K)]
    (N : Subrepresentation (Catalogue.representation D K h)) (hN : IsCoatom N)
    (hn : ¬ component D K ≤ N.quotientRepresentation.ker) :
    NaturalComponentRows (chiefRepresentation D K h N ⊤) (component D K) ∧
      centralizer (component D K : Set (actor D K)) = ⊥ := by
  have hH : D.H∈Chapter1.H G := by
    change D.QH≠⊥
    intro he
    have hp : D.V₁≤D.QH := (h.point_lt.le.trans (le_conjugateSpanBy _ _)).trans h.UH_le_QH
    have hz : D.V₁=⊥ := bot_unique (hp.trans_eq he)
    have hc := h.point_card
    rw [hz,card_bot] at hc
    contradiction
  let σ := chiefRepresentation D K h N ⊤
  have hi := d.third_index
  have hcardV := d.module_card
  have hcard := LocalGeometry.star_V_card_two h hi hU
  let : (starImage D.H K).Normal := Subgroup.Normal.map hnK _ (QuotientGroup.mk'_surjective _)
  let : (component D K).Normal := by
    change ((starImage D.H K).subgroupOf (actor D K)).Normal
    infer_instance
  let eK : component D K ≃* starImage D.H K := subgroupOfEquivOfLe le_sup_left
  let : IsSimpleGroup (component D K) := eK.isSimpleGroup
  let : IsQuasisimple (starImage D.H K) := s.quasisimple
  let : IsQuasisimple (component D K) := IsQuasisimple.of_mulEquiv eK.symm
  have hf : Function.Injective σ := top_section_faithful _ N
    (source_head_faithful d h hU K s hLK hnK N hN)
  have hirr : IsIrreducible σ := top_section_irreducible _ N hN
  have hnc : ¬ component D K ≤ σ.ker := top_section_noncentral _ N _ hn
  have hyp := source_chief_hypotheses_all D K h s d.hypothesis.qtke hH
    hi hU hcardV N ⊤ hnc hirr
  let : IsQuasisimple (generalizedFitting (actionImage σ)) := hyp.quasisimple
  have hfit := image_component_eq_fitting σ (component D K) hnc
  obtain ⟨hz,hcentral⟩ := centralizer_eq_bot_of_faithful_component σ (component D K) hf hfit
  let compAction := faithfulComponentActionEquiv σ (component D K) hf hfit
  obtain ⟨v,hv,hvo,P,hP⟩ := source_actor_marking d h hU K s
  obtain ⟨p,_⟩ := source_moved_plane d h hU K hLK v hv
  have hr : Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) = 2 := by
    change Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - LinearMap.id)) = 2
    rw [← fixedCodim_zpowers_eq_displacement_rank, hv, sourceRepresentation_eq h]
    exact Fitting.SourceAction.source_fixedCodim_two h hi hU hcardV
  have hlinear : ∀ n, (n=4 ∨ n=5) → ¬ Nonempty (ActionEquiv
      ((imageRepresentation σ).comp (generalizedFitting (actionImage σ)).subtype)
      (linearNatural BinaryField.two n)) := by
    rintro n hn' ⟨a⟩
    let b : ActionEquiv (σ.comp (component D K).subtype) (linearNatural BinaryField.two n) :=
      ⟨compAction.groupEquiv.trans a.groupEquiv,compAction.linearEquiv.trans a.linearEquiv,
        fun g w => (congrArg a.linearEquiv (compAction.intertwines g w)).trans (a.intertwines _ _)⟩
    have hvK : v ∈ component D K := mem_normal_of_centralizes_intrinsic_sylow_of_equiv
      (component D K) hcentral (b.groupEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear n))
      (BinaryLinear.OuterCyclic.sylow_fixing_inner hn') P v hP
    let vK : component D K := ⟨v,hvK⟩
    have hc : ∀ x ∈ P, x*vK = vK*x := fun x hx => Subtype.ext (hP x hx)
    exact Catalogue.LocalModels.noncentral_section_not_binaryNatural D K h s hcard
      (selected_section_even s) vK hv P hc hLK (fun _ => p) N ⊤ hnc hn' ⟨b⟩
  have hten : (actionImage σ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      Module.finrank (ZMod 2) ((⊤ : Subrepresentation (Catalogue.representation D K h)).toSubmodule ⧸
        (sectionLower (Catalogue.representation D K h) N ⊤).toSubmodule) ≠ 10 := by
    intro e
    exact noncentral_section_not_ten D K h s hcard (selected_section_even s) v hv
      (by simpa only [hvo] using pow_orderOf_eq_one v) hr N ⊤ hnc hirr
      ((faithfulImageEquiv σ hf).trans e)
  have sieve := source_chief_sieve D K h s d.hypothesis.qtke hH
    hi hU hcardV N ⊤ hnc hirr D.L₁ le_rfl c
  obtain ⟨t,hto,htr,_⟩ := source_chief_marked_all D K h s d.hypothesis.qtke hH
    hi hU hcardV N ⊤ hnc hirr
  have rows := natural_rows_of_chief_sieve (imageRepresentation σ) hyp sieve
    (fun F n hn' hdeg J => source_chief_not_unitary D K h s d.hypothesis.qtke hH
      hi hU hcardV N ⊤ hnc hirr F n hn' hdeg J) t hto htr hz hlinear hten
  refine ⟨?_,hcentral⟩
  rcases rows with ha | ha | ha <;> obtain ⟨a⟩ := ha
  · exact Or.inl ⟨⟨compAction.groupEquiv.trans a.groupEquiv,compAction.linearEquiv.trans a.linearEquiv,
      fun g w => (congrArg a.linearEquiv (compAction.intertwines g w)).trans (a.intertwines _ _)⟩⟩
  · exact Or.inr (Or.inl ⟨⟨compAction.groupEquiv.trans a.groupEquiv,compAction.linearEquiv.trans a.linearEquiv,
      fun g w => (congrArg a.linearEquiv (compAction.intertwines g w)).trans (a.intertwines _ _)⟩⟩)
  · exact Or.inr (Or.inr ⟨⟨compAction.groupEquiv.trans a.groupEquiv,compAction.linearEquiv.trans a.linearEquiv,
      fun g w => (congrArg a.linearEquiv (compAction.intertwines g w)).trans (a.intertwines _ _)⟩⟩)

end CFSG.Quasithin.Chapter13.Section05.A5Source
