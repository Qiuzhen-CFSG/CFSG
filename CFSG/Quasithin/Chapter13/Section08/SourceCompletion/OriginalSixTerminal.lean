module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalSixComponent
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalEarlierFlags
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalEarlierCore
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalTerminal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.TerminalModels

/-!
# The actual ordinary A₆ component is excluded at the source point normalizer

The original source geometry constructs the component's whole-module section,
the compatible point and edge markings, both preceding 13.7.6 implications,
the plane-core identity and the chief count. The completed ordinary terminal
argument then excludes this actual component of G₁. No terminal model,
strict denominator, component-section or earlier local clause is assumed.

The original natural setup and the exclusion of the other component rows
remain distinct duties of the full 13.8.1 source theorem.
Source: Aschbacher--Smith, 13.8.26,33--34, printed pp.962,966--969.
-/

public section
open Subgroup Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.SixAndG2

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ K : Subgroup G}

/-- The original A₆ component row at G₁, with every section and terminal
premise constructed on that same component and source flag. -/
theorem original_six_component_false_of_plane_noncentral
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ H ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hHz : G₁ ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKG : K ≤ G₁) (hK : (K.subgroupOf G₁).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) : False := by
  let := d.uh_elementary hHz
  have hF9 := hF9all G₁ hHz
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [← d.first_normalizer]
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer
    (localNaturalSetup d) eL hmax hm'
  have hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  have groups := ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.original_linear_group_facts
    d hmax hF9all hcentral hcomm
  have hN := groups.component_normal hHz hKG hK
  have hKT := groups.supplement hHz hKG hK
  have hjoin : G₁ = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
    apply le_antisymm
    · rw [hKT]
      exact sup_le_sup le_rfl le_sup_right
    · exact sup_le hKG hHz.1.2
  have hqs := (SolvableSource.component_fitting_source d hmax hF9all hcentral hcomm
    (Components.EarlierResidual.original_source d hmax) hHz K hK).2
  obtain ⟨a⟩ := SolvableExclusion.Five.exists_starAction G₁ (Source.UH G₁ V₃) V₁
    (le_normalizer_conjugateSpanBy V₃ G₁)
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  let ρ := A6Endgame.IntersectionBalance.tildeRepresentation G₁ (Source.UH G₁ V₃) V₁ a
  have hρ : IsConjugation G₁ V₃ V₁ ρ := TerminalPoint.starAction_isConjugation a
  obtain ⟨eK',hs,_⟩ := original_six_component_models_of_plane_noncentral
    d eL hmax hF9all hm hHz hKG hK eK ρ hρ
  have flags := original_earlier1376_of_ordinary_plane_noncentral d eL hmax hF9all hm
  have models := SourceAssembly.TerminalModels.ordinary_terminal_models d flags hHz hF9
    hcomm hKG hK hN hKT a eK' hs
  have hres : sourceOne L T V₁ = TransvectionParabolic.EarlierCore.localResidual L V₁ :=
    TransvectionParabolic.EarlierCore.residual_relative_normalizer_eq L T V₁
      T.isPGroup' d.normalizes_L d.line_stable
  have flags' : TransvectionParabolic.Marking.NaturalSection.Earlier1376 L
      (TransvectionParabolic.EarlierCore.localResidual L V₁) T
      (normalizer (V₁ : Set G)) M V₂ V₃ V₁ := by
    simpa only [← hres,← d.first_normalizer] using flags
  exact OrdinaryAssembly.contradiction_of_original_local_endgame d eL hHz hF9
    hcentral hcomm hjoin hK hN hqs inferInstance a models eK' hs
    (original_earlier1354_of_ordinary_plane_noncentral (localNaturalSetup d) eL hm)
    flags' (original_earlier1376_chief_of_ordinary_plane_noncentral d eL hmax hF9all hm)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
