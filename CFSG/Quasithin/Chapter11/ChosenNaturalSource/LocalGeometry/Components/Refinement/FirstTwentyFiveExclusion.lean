module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.PointResidual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstRee

/-!
# The first-normalizer sieve after excluding PSL₂(25)

Apply the point-fixer contradiction to the actual PSL₂(25) row in the existing
Cartan sieve. The preceding hypotheses, normality relative to N_G(V₁), literal
Cartan factor and full component-embedding disjunction are retained.
The remaining exceptional quotient models are the field-four linear models,
signed ternary field-five models, and J₁. Their subsequent source arguments
remain with the same relative-component assembly owner.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
proof of 11.1.2, printed p.762.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Remove the square-field rank-one row in the literal Cartan consumer. -/
theorem first_refinement_or_ternary_or_janko_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : ComponentAlternative (f.Li 0) K S.field.degree) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      (S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨
        (∃ u, Chapter1.Section02.LocalModels.IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨
          Chapter1.Section02.LocalModels.IsSLSign (K ⧸ pCore 2 K) u 3 5) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model))) := by
  rcases first_refinement_or_fieldFour_models_of_cartan D S f hu hm hfix hX hK hLK
    hXcard hfaith hk with h | ⟨hn,h⟩
  · exact .inl h
  · refine .inr ⟨hn,?_⟩
    rcases h with h | h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact (first_component_not_twentyFive D S f hm hn hfix hK.1 hLK h).elim
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
