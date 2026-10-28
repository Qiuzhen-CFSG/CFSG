module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryChosenSetup
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceChoice
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySixSeed

/-!
# Seed closure from the original ordinary A₆ module choice

The maximal source subgroup supplies the Chapter12 hypothesis and an actual
Irr⁺ member. Its earlier natural-module conclusion constructs the same
NaturalSetup and its full invariant flag. The completed 13.5.12 theorem
then makes the point-normalizer seed closure abelian. No chosen subgroup,
flag, local setup, F.9 application or closure conclusion is an extra premise.
The natural-module classification and its T-invariance remain the genuine
preceding source input on the actual chosen module.
Source: Aschbacher--Smith13.3.2(3),13.5.12 and13.7.2, pp.885,918,935--936.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The same chosen module supplies both its flag and the source seed closure. -/
theorem exists_original_six_abelian_seed
    (hmax : Maximal (Counterexample T) L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hmodel : Chapter6.Source.IsConjugationModel L V
      (alternatingNaturalRepresentation (Fin 6))) :
    ∃ V₁ V₂ V₃ : Subgroup G, Nonempty
      (NaturalSetup T L V V₁ V₂ V₃ (normalizer (L : Set G)) (normalizer (V₁ : Set G))) ∧
      IsMulCommutative (conjugateSpanBy V₃ (normalizer (V₁ : Set G))) := by
  obtain ⟨V₁,V₂,V₃,⟨d⟩⟩ := exists_original_six_setup_of_chosen_module hmax.1 D hTV hmodel
  obtain ⟨e,_,_⟩ := hmodel
  exact ⟨V₁,V₂,V₃,⟨d⟩,original_six_seed_span_abelian d hmax e⟩

/-- Actual source entry: construct the Irr⁺ member before using its preceding
natural-module classification, then apply the complete seed-closure theorem. -/
theorem exists_original_six_abelian_seed_of_source
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (modules : ∀ V : Subgroup G, Chapter12.Section02.ChosenModule T L V →
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
        Chapter6.Source.IsConjugationModel L V (alternatingNaturalRepresentation (Fin 6))) :
    ∃ V V₁ V₂ V₃ : Subgroup G, Nonempty
      (NaturalSetup T L V V₁ V₂ V₃ (normalizer (L : Set G)) (normalizer (V₁ : Set G))) ∧
      IsMulCommutative (conjugateSpanBy V₃ (normalizer (V₁ : Set G))) := by
  obtain ⟨_,_,V,⟨D⟩⟩ := original_six_chosen_source hmax e
  obtain ⟨hTV,hmodel⟩ := modules V D
  exact ⟨V,exists_original_six_abelian_seed hmax D hTV hmodel⟩

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
