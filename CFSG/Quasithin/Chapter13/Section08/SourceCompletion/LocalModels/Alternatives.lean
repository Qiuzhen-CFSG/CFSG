module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Ordinary
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Covered
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.SourceInputs

/-!
# Actual ordinary or covered local flag models

The component central-cover alternative is marked over the original
six-letter projection. In each case its module coordinates are the
original V, and its point, plane and seed spaces pull back to the
unchanged Sylow-stable V₁,V₂,V₃. Thus the `natural_models` input of the
13.8.5 solvable branch follows from the standing setup, with no selected
model assumed. The separate 13.2.2(3),(9) factorization and normalizer
conclusions remain to be proved from their source hypotheses.

Source: Aschbacher–Smith, Notation 13.2.1, 13.2.2 and 13.8.5,
printed pp.877–878,947.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

variable {G : Type*} [Group G] [Finite G]

/-- The two compatible natural-model alternatives for the literal local setup. -/
theorem local_flag_alternatives {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    Nonempty (TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃) ∨
      Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) := by
  rcases local_quotient_alternatives d with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl (local_ordinary_flag_model d e he)
  · exact Or.inr (local_covered_flag_model d e he)

/-- The exact universal `natural_models` field of `EarlierLocalInputs`. -/
theorem earlier_natural_models :
    ∀ (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G),
      LocalSetup T L V V₁ V₂ V₃ M G₁ →
      Nonempty (TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃) ∨
        Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) := by
  intro T L V V₁ V₂ V₃ M G₁ d
  exact local_flag_alternatives d

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
