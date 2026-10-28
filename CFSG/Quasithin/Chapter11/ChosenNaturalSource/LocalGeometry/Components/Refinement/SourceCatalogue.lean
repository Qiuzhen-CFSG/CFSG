module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SourceCatalogue
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstSpecialLinear

/-!
# First-normalizer sieve from the preceding flag and Cartan facts

The full relative-component embedding classification supplies the 11.1.1
alternative to the checked first-normalizer sieve. Its conclusion retains
exactly the prime SL₂, prime PSL₂ and literal PGL₃(4) quotient alternatives;
no exhaustive carrier-list premise remains. The existential application
also constructs the containing component and its normality in N_G(V₁).

The preceding flag quotient, pointwise line action, Cartan factor and
Sylow-normalizer facts are supplied by qt-d-1222-natural-flag-cartan and
qt-d-1222-natural-preliminary-source, with final discharge owned by
qt-d-1222-natural-local-geometry. The additional field-four triangle clauses
and the second-normalizer argument remain with
qt-d-1222-natural-relative-components. This does not assert the full
Proposition 11.1.2 before those clauses have been proved.

Source: Aschbacher--Smith 11.1.1--11.1.2, printed pp.761--765,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The first-index sieve now needs only preceding local facts, with the
entire embedding classification discharged using the actual quotient. -/
theorem first_reduction_from_preceding_inputs
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    RefinementReduction L (f.Li 0) (f.Li 1) K X 0 S.field.degree :=
  first_reduction_of_cartan D S f hu hm hfix hNT hX hK hLK hXcard hfaith
    (Embedding.flag_component_alternative D S f 0 hm hK.1 hLK)

/-- Construct the relatively normal containing component and apply the
first-index sieve, preserving He membership and all quotient alternatives. -/
theorem first_exists_normal_component_reduction
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    {X : Subgroup G} (hX : IsCartan T L X)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K ∧
      f.Li 0 ≤ K ∧ K ∈ Chapter1.He G ∧
      RefinementReduction L (f.Li 0) (f.Li 1) K X 0 S.field.degree := by
  obtain ⟨K,hK,hLK,hHe,_⟩ := flag_exists_unique_normal_component_of_model D S f 0 hm
  exact ⟨K,hK,hLK,hHe,
    first_reduction_from_preceding_inputs D S f hu hm hfix hNT hX hK hLK hXcard hfaith⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
