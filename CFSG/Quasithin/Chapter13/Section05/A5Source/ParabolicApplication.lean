module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentConfiguration
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalRecognition
public import Theory.Representation.BinaryFullPlane
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.CentralQuotient
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.SixGeneration
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.EightMarking
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic

/-!
# The original A₅ marked parabolic applications

The source seed is a fully moved binary plane, hence irreducible. The proved
normal branch supplies the normalizer control that makes the original local
residual act nontrivially on the selected component. The three natural central
quotient models then identify the marked parabolic and generate the whole
original tilde module by the same local residual.
Source: Aschbacher–Smith13.5.21(5–6), printed p.924.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open ComponentReduction Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- The F.9 seed conditions for the original chosen A₅ module. -/
theorem local_seed_module_conditions (hU : ¬ IsMulCommutative D.UH) :
    ModuleConditions D h := by
  apply source_module_conditions h d.third_index hU d.module_card
  have hs : D.Vplus = ⁅D.V,D.L₁⁆ := d.third_eq_commutator
  conv_rhs => rw [hs]
  rw [commutator_isPPerfect_idempotent D.L₁ D.V
    (isPPerfect_embedded_pResidual 2 _) (IsElementaryAbelian.isPGroup 2 D.V)
    ((map_subtype_le _).trans (inf_le_left.trans d.chosen.normalizes))]
  exact d.third_eq_commutator

/-- Full movement on a binary plane proves irreducibility for L₁*T*. -/
theorem source_local_seed_irreducible (hU : ¬ IsMulCommutative D.UH) :
    ∃ S : Subrepresentation ((Action.starRepresentation D h).comp (localStar D).subtype),
      S.toSubmodule = Action.seedSpace D ∧ IsIrreducible S.toRepresentation := by
  let S : Subrepresentation ((Action.starRepresentation D h).comp (localStar D).subtype) :=
    ⟨Action.seedSpace D,fun g _ hw => (localStar_stabilizes_seed D h g.property _).mpr hw⟩
  refine ⟨S,rfl,?_⟩
  have hm := local_seed_module_conditions d h hU
  have hfull : subspaceCommutator (Action.starRepresentation D h)
      (Action.seedSpace D) (localStar D) = Action.seedSpace D := by
    apply le_antisymm (subspaceCommutator_le_of_invariant _ (localStar_stabilizes_seed D h))
    calc
      Action.seedSpace D = subspaceCommutator (Action.starRepresentation D h)
          (Action.seedSpace D) (starImage D.H D.L₁) := hm.2.1.symm
      _ ≤ _ := by
        apply Submodule.span_mono
        rintro _ ⟨x,hx,v,hv,rfl⟩
        exact ⟨x,mem_sup_left hx,v,hv,rfl⟩
  apply irreducible_of_rank_two_full_movement _ hm.2.2
  apply Submodule.map_injective_of_injective S.toSubmodule.injective_subtype
  rw [BinaryGroupAction.subrepresentation_moved_map,Submodule.map_top,
    Submodule.range_subtype]
  change subspaceCommutator ((Action.starRepresentation D h).comp (localStar D).subtype)
    (Action.seedSpace D) ⊤ = Action.seedSpace D
  rw [BinaryParabolicNatural.commutator_comp,←MonoidHom.range_eq_map,Subgroup.range_subtype,hfull]

variable
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T
    (centralizer (D.V₁ : Set G)) (normalizer (D.L : Set G)))
  (hnot : ¬ ModelConclusion G 5)
include hA312 hH hnot

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- The original local residual acts nontrivially on the selected component. -/
theorem source_local_component_commutator
    (K : Subgroup G) (s : Selected D K) :
    ⁅starImage D.H K,starImage D.H D.L₁⁆ ≠ ⊥ := by
  obtain ⟨himage,hcore⟩ := source13_5_19 d hA312 hH
    (fun J hJ hu hn => source13_5_17 d hA312 hJ hu hn) hnot
  rw [(selected_local_commutators s h d.hypothesis.qtke hH.1.1
    D.L₁ le_rfl himage hcore).2]
  intro he
  exact s.moved (by rw [he,commutator_bot_left])

/-- Both marked parabolic and whole-module conclusions in the S₆ case. -/
theorem symmetric_six_source_conclusions (hU : ¬ IsMulCommutative D.UH)
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (f : Catalogue.actor D K ≃* Equiv.Perm (Fin 6))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (f b) (centralProjection D h fV u)) :
    (starImage D.H D.T).relIndex (markedParabolic D h K) = 3 ∧
      localStar D = markedParabolic D h K ∧
      (pResidual 2 (markedParabolic D h K)).map (markedParabolic D h K).subtype =
        starImage D.H D.L₁ ∧ D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆ := by
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.hypothesis.qtke hH.1.1).stronglyQuasithin
  have hm := source_local_component_commutator d h hA312 hH hnot K s
  obtain ⟨S,hS,hirr⟩ := source_local_seed_irreducible d h hU
  let := hirr
  have hmodule := local_seed_module_conditions d h hU
  have hp := symmetric_six_marked_parabolic D h s d.hypothesis.qtke.properK hSQ
    hLK hm S hS hmodule.2.2 hmodule.2.1.symm f fV hfV
  exact ⟨hp.1,hp.2.1,hp.2.2,
    symmetric_six_tilde_generation D h s d.hypothesis.qtke.properK hSQ
      hLK d.third_eq_commutator hm S hS hmodule.2.2 hmodule.2.1.symm f fV hfV⟩

/-- The whole original tilde module is generated by L₁ in the A₈ case. -/
theorem alternating_eight_source_generation (hU : ¬ IsMulCommutative D.UH)
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (f : Catalogue.actor D K ≃* alternatingGroup (Fin 8))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (f b)
          (centralProjection D h fV u)) :
    D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆ := by
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.hypothesis.qtke hH.1.1).stronglyQuasithin
  exact alternating_eight_tilde_generation D h s d.hypothesis.qtke.properK hSQ hLK
    (source_local_component_commutator d h hA312 hH hnot K s)
    d.third_index hU d.third_eq_commutator f fV hfV

/-- Both marked parabolic and whole-module conclusions in the G₂ case. -/
theorem g2_source_conclusions (hU : ¬ IsMulCommutative D.UH)
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (hn : (starImage D.H K).Normal)
    (f : Catalogue.actor D K ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      fV (CentralQuotient.representation D h K hn b.val u) =
        g2DerivedNatural (ZMod 2) (f b) (fV u)) :
    (starImage D.H D.T).relIndex (markedParabolic D h K) = 3 ∧
      localStar D = markedParabolic D h K ∧
      (pResidual 2 (markedParabolic D h K)).map (markedParabolic D h K).subtype =
        starImage D.H D.L₁ ∧ D.UH = ⁅D.QH,K⁆ ∧
      D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆ := by
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.hypothesis.qtke hH.1.1).stronglyQuasithin
  have hm := source_local_component_commutator d h hA312 hH hnot K s
  have hmodule := local_seed_module_conditions d h hU
  exact G2Parabolic.source_conclusions D h K s d.hypothesis.qtke.properK hSQ d.third_index hU
    hLK d.third_eq_commutator hm (selected_actor_normalization s h d.third_index hU).2
    hmodule.2.2 hmodule.2.1.symm f (CentralQuotient.centralSubrepresentation D h K hn)
    rfl fV hfV
end CFSG.Quasithin.Chapter13.Section05.A5Source
