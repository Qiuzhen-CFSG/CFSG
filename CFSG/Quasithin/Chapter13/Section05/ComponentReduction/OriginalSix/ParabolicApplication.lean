module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CentralQuotient
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.SixGeneration
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic

/-!
# The original S₆ and G₂ parabolic applications

The original point-residual orbit proves irreducibility of the seed for
L₁*T*. Its commutator generation and dimension are the proved F.9 module
conditions. Applying the natural central-quotient coordinates to the two
existing model calculations identifies the marked parabolic and generates
the entire original U_H/V₁ by L₁*. The conclusion is transported through
the literal ambient tilde map used in13.5.14.
Source: Aschbacher–Smith13.5.21(5–6), printed p.924.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Section08.Source Recognition Recognition.Configuration
open Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking
open Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h

/-- The actual seed is irreducible for the whole original local product. -/
theorem source_local_seed_irreducible (hU : ¬IsMulCommutative D.UH) :
    ∃ S : Subrepresentation ((Action.starRepresentation D h).comp (localStar D).subtype),
      S.toSubmodule = Action.seedSpace D ∧ IsIrreducible S.toRepresentation := by
  let S : Subrepresentation ((Action.starRepresentation D h).comp (localStar D).subtype) :=
    ⟨Action.seedSpace D,fun g _ hw => (localStar_stabilizes_seed D h g.property _).mpr hw⟩
  refine ⟨S,rfl,?_⟩
  have hm := source_module_conditions h (NormalBranch.SourceOrthogonal.seed_index d) hU
    (NormalBranch.ReturningPlane.module_card d)
    (by rw [residual_eq_sourceOne d h];exact (Section07.ModelExclusions.seed_commutator_point_residual d).symm)
  have hdim : Module.finrank (ZMod 2) S.toSubmodule=2 := hm.2.2
  let : Nontrivial S.toSubmodule := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) S.toSubmodule)
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun W => ?_⟩
  by_cases hW : W=⊥
  · exact Or.inl hW
  right
  apply top_unique
  intro w _
  by_cases hw0 : w=0
  · rw [hw0];exact W.toSubmodule.zero_mem
  obtain ⟨u,hu,hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (show W.toSubmodule≠⊥ from fun he => hW (Subrepresentation.toSubmodule_injective he))
  let : (D.V₁.subgroupOf (Section08.Source.UH D.H D.Vplus)).Normal := inferInstanceAs ((D.V₁.subgroupOf D.UH).Normal)
  let : IsElementaryAbelian 2 (Section08.Source.Utilde D.H D.Vplus D.V₁) := inferInstanceAs (IsElementaryAbelian 2 (Action.ModuleGroup D))
  have hLH : sourceOne D.L D.T D.V₁ ≤ D.H :=
    (residual_eq_sourceOne d h).symm ▸ (le_sup_left.trans h.local_le)
  have hρ : IsConjugation D.H D.Vplus D.V₁ (Action.starRepresentation D h) := Action.starRepresentation_apply D h
  obtain ⟨l,hl⟩ := Section07.ModelExclusions.seed_section_nonzero_orbit d hLH
    (Action.starRepresentation D h) hρ u.val u.property
    (fun he => hu0 (Subtype.ext he)) w.val w.property (fun he => hw0 (Subtype.ext he))
  let a : localStar D := ⟨QuotientGroup.mk' (pCore 2 D.H) (inclusion hLH l),
    (show starImage D.H D.L₁ ≤ localStar D from le_sup_left)
      (mem_map_of_mem _ ((residual_eq_sourceOne d h).symm ▸ l.property))⟩
  have hh := W.apply_mem_toSubmodule a hu
  have he : S.toRepresentation a u=w := Subtype.ext hl
  exact he ▸ hh

variable (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
include e

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- The original local residual acts nontrivially on the selected component. -/
theorem source_local_component_commutator
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G))
    (K : Subgroup G) (s : Selected D K) :
    ⁅starImage D.H K,starImage D.H D.L₁⁆ ≠ ⊥ := by
  obtain ⟨himage,hcore⟩ := normalizer_conclusions d h e h1221 hc
  rw [(selected_local_commutators s h d.counterexample.qtke (selected_H_mem h)
    D.L₁ le_rfl himage hcore).2]
  intro he
  exact s.moved (by rw [he,commutator_bot_left])

/-- Both marked-parabolic and whole-module conclusions in the literal S₆ branch. -/
theorem symmetric_six_source_conclusions (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G))
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (f : Catalogue.actor D K ≃* Equiv.Perm (Fin 6))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (f b) (centralProjection D h fV u)) :
    (starImage D.H D.T).relIndex (markedParabolic D h K) = 3 ∧
      localStar D = markedParabolic D h K ∧
      (pResidual 2 (markedParabolic D h K)).map (markedParabolic D h K).subtype =
        starImage D.H D.L₁ ∧
      D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆ := by
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.counterexample.qtke (selected_H_mem h)).stronglyQuasithin
  have hm := source_local_component_commutator d h e h1221 hc K s
  obtain ⟨S,hS,hirr⟩ := source_local_seed_irreducible d h hU
  let := hirr
  have hmodule := source_module_conditions h (NormalBranch.SourceOrthogonal.seed_index d) hU
    (NormalBranch.ReturningPlane.module_card d)
    (by rw [residual_eq_sourceOne d h];exact (Section07.ModelExclusions.seed_commutator_point_residual d).symm)
  have hpar := symmetric_six_marked_parabolic D h s d.counterexample.qtke.properK hSQ
    hLK hm S hS hmodule.2.2 hmodule.2.1.symm f fV hfV
  exact ⟨hpar.1,hpar.2.1,hpar.2.2,
    symmetric_six_tilde_generation D h s d.counterexample.qtke.properK hSQ
      hLK (seed_identity d h) hm S hS hmodule.2.2 hmodule.2.1.symm f fV hfV⟩

/-- Both marked-parabolic and whole-module conclusions in the literal G₂ branch. -/
theorem g2_source_conclusions (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G))
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
  have hi := NormalBranch.SourceOrthogonal.seed_index d
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.counterexample.qtke (selected_H_mem h)).stronglyQuasithin
  have hm := source_local_component_commutator d h e h1221 hc K s
  have hmodule := source_module_conditions h hi hU (NormalBranch.ReturningPlane.module_card d)
    (by rw [residual_eq_sourceOne d h];exact (Section07.ModelExclusions.seed_commutator_point_residual d).symm)
  exact G2Parabolic.source_conclusions D h K s d.counterexample.qtke.properK hSQ hi hU
    hLK (seed_identity d h) hm (selected_actor_normalization s h hi hU).2
    hmodule.2.2 hmodule.2.1.symm f (CentralQuotient.centralSubrepresentation D h K hn)
    rfl fV hfV
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
