module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalLinearComponent
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalSevenComponent
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalSixTerminal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.OriginalG2

/-!
# The original ordinary source contradiction after all component rows

Select an actual component of the original point normalizer. The completed
source catalogue leaves binary linear, A₆, A₇ and derived G₂ rows. The actual
ordinary linear and seven-point proofs exclude their rows without a universal
local-input family. The A₆ proof constructs its entire terminal model, while
the G₂ proof constructs its literal quotient action, quadratic orbit data and
parabolic contradiction. Thus no component row, section or terminal model is
an extra hypothesis.

The preceding natural setup, F.9 applicability and plane movement retain
their original source duties. The covered local quotient remains separate.
Source: Aschbacher--Smith 13.8.19--34, printed pp.953--969.
-/

public section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- The actual ordinary point-normalizer source is impossible after the
complete component catalogue, with all row proofs constructed internally. -/
theorem original_ordinary_false_of_plane_noncentral
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hHz : G₁ ∈ Source.Hz (sourceOne L T V₁) T G₁ M) : False := by
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
  obtain ⟨K,hKG,hK,_⟩ := Components.original_exists_normal_component
    d hmax hF9all hcentral hcomm hHz
  have components := FieldComponents.LinearThree.OriginalExclusion.original_component_conclusions
    d hmax hF9all hcentral hcomm
  rcases components.models hHz hKG hK with ⟨n,hn₀,hn₁,hlin⟩ | ⟨eK⟩ | ⟨eK⟩ | ⟨eK⟩
  · exact original_linear_component_false_of_plane_noncentral
      d eL hmax hF9all hm hHz hKG hK hn₀ hn₁ hlin
  · obtain ⟨eK⟩ := eK
    exact original_six_component_false_of_plane_noncentral d eL hmax hF9all hm hHz hKG hK eK
  · obtain ⟨eK⟩ := eK
    exact original_seven_component_false_of_plane_noncentral d eL hmax hF9all hm hHz hKG hK eK
  · obtain ⟨eK⟩ := eK
    let := d.uh_elementary hHz
    have hF9 := hF9all G₁ hHz
    have groups := FieldComponents.LinearThree.OriginalExclusion.original_linear_group_facts
      d hmax hF9all hcentral hcomm
    have hN := groups.component_normal hHz hKG hK
    have hKT := groups.supplement hHz hKG hK
    have hjoin : G₁ = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
      apply le_antisymm
      · rw [hKT]
        exact sup_le_sup le_rfl le_sup_right
      · exact sup_le hKG hHz.1.2
    obtain ⟨hfit,hUK,P,hP⟩ := SixAndG2.SourceAssembly.original_component_structure
      d hmax hF9all hcentral hcomm hHz hKG hK
    let act := Comparison.conjugationAction (d.line_le_uh G₁) hF9.plus_le_H
      (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
      hF9.commutator_UH_QH_le_point
    have orbit := SixAndG2.SourceAssembly.g2_orbit_inputs_from_quadratic_actor d hHz hF9
      hKG hK hN hjoin hfit hUK hcentral hcomm act.representation act.conjugation P hP eK
    exact SixAndG2.SourceAssembly.g2_exclusion d hHz hF9 rfl hKG hK hN hjoin
      hfit hUK hcentral hcomm act.representation act.conjugation P hP orbit eK

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
