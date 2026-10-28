module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBaumannSource
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryChosenSetup
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceEscape

/-!
# The original selected ordinary A₆ entry to Section 13.8

The earlier escape theorem is applied to the actual maximal counterexample
and its unchanged chosen module. It selects the point normalizer itself in
Hz. The completed ordinary Baumann argument gives abelianness of the full
span, hence of every smaller Hz span. The literal F.9 construction and
critical-pair theorem then supply the original odd paths and reoriented
geometry for every member of that same family.

The second theorem starts with an existential natural Irr⁺ choice. It
constructs the flag and its equivariant NaturalSetup, so the source producer
may reselect its module; no claim about all original Irr⁺ choices is needed.
The natural-module choice, 13.3.2 catalogues, 13.3.14 plane noncentrality and
12.2.13 escape theorem remain explicit earlier inputs. Their producers must
supply them before this conditional assembly proves the original source.

Source: Aschbacher--Smith, 13.3.6, 13.3.14, 13.7.8 and 13.8.2--8,
printed pp.886,891--893,940--949 (combined manuscript, 1 March 2004).
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
theorem original_six_selected_source_inputs
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    G₁ ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M ∧
      IsMulCommutative (conjugateSpanBy V G₁) ∧
      ∀ H ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M,
        (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis ∧
        IsMulCommutative (Chapter13.Section08.Source.VH H V) ∧
        ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) H V,
          Odd c.path.length ∧
          Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c V₃ V₁ ∧
          ¬ ⁅c.Ugamma V₃,V⁆ ≤ c.Aone V₁ := by
  have hspan := original_six_full_span_abelian d hmax eL hm h1332 modules
  refine ⟨original_six_point_normalizer_mem_Hz d hmax eL escape, hspan, ?_⟩
  intro H hH
  have hF9 := original_six_f9_of_source d hmax eL hm hH
  let : IsMulCommutative (conjugateSpanBy V G₁) := hspan
  exact ⟨hF9, conjugateSpanBy_isMulCommutative_of_le le_rfl hH.2.1,
    d.exists_earlierGeometry hspan hF9⟩

/-- Construct the flag and the ordinary source applications from one actual
natural chosen module. An earlier source may reselect this Irr⁺ member. -/
theorem exists_original_six_selected_source_inputs
    (hmax : Maximal (Counterexample T) L)
    (natural : ∃ V : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T L V) ∧
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      Chapter6.Source.IsConjugationModel L V
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)))
    (plane : ∀ (V V₁ V₂ V₃ : Subgroup G),
      NaturalSetup T L V V₁ V₂ V₃ (normalizer (L : Set G)) (normalizer (V₁ : Set G)) →
        ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u}) :
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
    original_six_selected_source_inputs d hmax eL (plane V V₁ V₂ V₃ d) h1332 modules escape⟩

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
