module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceAssembly
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBaumannSourceAt
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceEscapeAt
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBaumannSource
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryChosenSetup
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceEscape

/-!
# Original selected ordinary source inputs with local earlier premises

Local 12.2.13 applied to the actual chosen module puts its point normalizer
in Hz. The local A₅ module theorem and original Baumann bound prove abelianness
of the full span. Every member of the same Hz family inherits an abelian span,
F.9 applicability and the original odd critical path with reoriented geometry.
The existential version builds the flag from one natural Irr⁺ choice and
preserves that same module throughout; no universal natural-choice assertion
is inferred.

Plane noncentrality, the earlier local module inputs and the natural choice
remain explicit with qt-d-13314-ordinary-blocks, qt-d-1222-source and
qt-d-1332-source. Final source assembly stays in qt-d-1378-source and
qt-d-1381-source.
Source: Aschbacher–Smith 13.3.6,13.3.14,13.7.8,13.8.2–8, pp.886,891–893,940–949.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion Chapter13.Section07
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- Select the actual point normalizer and supply all original Section 13.8
opening inputs uniformly over its unchanged Hz family. -/
theorem original_six_selected_source_inputs_at
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T) :
    G₁ ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M ∧
      IsMulCommutative (conjugateSpanBy V G₁) ∧
      ∀ H ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M,
        (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis ∧
        IsMulCommutative (Chapter13.Section08.Source.VH H V) ∧
        ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) H V,
          Odd c.path.length ∧
          Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c V₃ V₁ ∧
          ¬ ⁅c.Ugamma V₃,V⁆ ≤ c.Aone V₁ := by
  have hspan := original_six_full_span_abelian_at d hmax eL hm h1332 modules
  refine ⟨original_six_point_normalizer_mem_Hz_at d hmax eL escape, hspan, ?_⟩
  intro H hH
  have hF9 := original_six_f9_of_source d hmax eL hm hH
  let : IsMulCommutative (conjugateSpanBy V G₁) := hspan
  exact ⟨hF9, conjugateSpanBy_isMulCommutative_of_le le_rfl hH.2.1,
    d.exists_earlierGeometry hspan hF9⟩

/-- Construct the flag and the ordinary source applications from one actual
natural chosen module. An earlier source may reselect this Irr⁺ member. -/
theorem exists_original_six_selected_source_inputs_at
    (hmax : Maximal (Counterexample T) L)
    (natural : ∃ V : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T L V) ∧
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      Chapter6.Source.IsConjugationModel L V
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)))
    (plane : ∀ (V V₁ V₂ V₃ : Subgroup G),
      NaturalSetup T L V V₁ V₂ V₃ (normalizer (L : Set G)) (normalizer (V₁ : Set G)) →
        ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T) :
    ∃ V V₁ V₂ V₃ : Subgroup G,
      Nonempty (NaturalSetup T L V V₁ V₂ V₃
        (normalizer (L : Set G)) (normalizer (V₁ : Set G))) ∧
      normalizer (V₁ : Set G) ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T
        (normalizer (V₁ : Set G)) (normalizer (L : Set G)) ∧
      IsMulCommutative (conjugateSpanBy V (normalizer (V₁ : Set G))) ∧
      ∀ H ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T
          (normalizer (V₁ : Set G)) (normalizer (L : Set G)),
        (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis ∧
        IsMulCommutative (Chapter13.Section08.Source.VH H V) ∧
        ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) H V,
          Odd c.path.length ∧
          Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c V₃ V₁ ∧
          ¬ ⁅c.Ugamma V₃,V⁆ ≤ c.Aone V₁ := by
  obtain ⟨V,⟨D⟩,hTV,hmodel⟩ := natural
  obtain ⟨V₁,V₂,V₃,⟨d⟩⟩ := exists_original_six_setup_of_chosen_module hmax.1 D hTV hmodel
  obtain ⟨eL,_,_⟩ := hmodel
  exact ⟨V,V₁,V₂,V₃,⟨d⟩,
    original_six_selected_source_inputs_at d hmax eL (plane V V₁ V₂ V₃ d) h1332 modules escape⟩

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
