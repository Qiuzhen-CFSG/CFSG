module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint.Source

/-!
# The original ordinary A₆ assembly with constructed terminal point models

At the actual maximal ordinary source choice, the existing escape and
abelian-closure theorems supply H=G₁, F.9, the full elementary span and the
ambient seed centralizer bound. The terminal construction now supplies the
point-model callback for every strict critical pair from the recognized
component section, with no movement or nonfixedness assumptions.

The earlier 13.8.21/26/27 component, section and edge marking remain explicit,
as does the independent 13.8.33 equality-case input. Their assembly owners
must discharge them before this becomes the unconditional 13.8.1 theorem.
Source: Aschbacher--Smith, printed pp.946--949,957,962--969.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
open CriticalGeometry TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Chapter14.Section08.LieTypeBranch
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ K : Subgroup G}

/-- Apply the constructed terminal point models to the unchanged original
maximal ordinary setup and the existing final case split. -/
theorem contradiction_of_original_source_sections
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hgen : G₁ = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf G₁).IsCComponent) (hN : (K.subgroupOf G₁).Normal)
    (hqs : IsQuasisimple (Source.starImage G₁ K))
    (hU : IsElementaryAbelian 2 (Source.UH G₁ V₃))
    (a : letI := hU
      SolvableExclusion.Five.StarAction G₁ (Source.UH G₁ V₃) V₁)
    (models : letI := hU
      TerminalRanks.MarkedModels G₁ ((L ⊔ (T : Subgroup G)) ⊓ G₁) V₃ V₁)
    (hUK : Source.UH G₁ V₃ = ⁅Source.UH G₁ V₃,K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* A6)
    (hs : letI := hU
      HasSectionModel G₁ V₃ V₁ (A6Endgame.IntersectionBalance.tildeRepresentation G₁ (Source.UH G₁ V₃) V₁ a)
        K (show K ≤ G₁ from hgen ▸ le_sup_left) (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK)
    (case_one : ∀ c : CriticalPair L (T : Subgroup G) G₁ V,
      (Source.DH (Source.UH G₁ V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH G₁ V₃ ∨
        Source.Dgamma (c.Ugamma V₃) (Source.UH G₁ V₃) V₁ = c.Ugamma V₃) →
      CaseAssembly.CaseOneModels T L G₁ V₃ V V₁) : False := by
  let : IsElementaryAbelian 2 (Source.UH G₁ V₃) := hU
  have hHz := original_six_point_normalizer_mem_Hz d hmax eL escape
  have hspan := original_six_full_span_abelian d hmax eL hm h1332 modules
  let dl := d.toLocalSetup hspan
  have hF9 := original_six_f9_of_source d hmax eL hm hHz
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer d eL
    (hypothesis1221_of_maximal_natural_six d hmax eL)
    (by rwa [← d.first_normalizer])
  have hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  apply CaseAssembly.contradiction_of_source_cases dl hHz hF9 rfl hgen hK hN hqs
    hcentral hcomm models case_one
  intro c hstrict _ hline
  exact TerminalPoint.point_models_of_component_section dl hHz hF9 c rfl hstrict
    hcomm a (show K ≤ G₁ from hgen ▸ le_sup_left) hK hN hUK eK hs hline

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
