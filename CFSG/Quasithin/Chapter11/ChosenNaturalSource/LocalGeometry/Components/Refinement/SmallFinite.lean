module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SmallFinite
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstJanko

/-!
# First-normalizer refinement for A₇, 3.A₇ and J₁

The actual rank-one section forces field four in all three carriers.
The literal Cartan centralizer then has order three and is faithful on
V₁. Its outside cubic excludes both alternating-seven rows, including
the central cover. In J₁, generation by the marked A₅ section and the
Sylow normalizer puts the containing component in N_G(L), forcing
equality. No exhaustive embedding-list or field-degree premise is used.

The preceding flag and Cartan inputs belong to
qt-d-1222-natural-flag-cartan, and the Sylow-normalizer bound to
qt-d-1222-natural-line-action. Their final discharge belongs to
qt-d-1222-natural-local-geometry. The relative-components owner retains
the remaining carriers, second-index sieve and triangle.
Source: Aschbacher--Smith 11.1.1--11.1.2, printed pp.761--762,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Equality in all three small finite rows, derived from their actual
section parameters and the original Cartan and Sylow-normalizer facts. -/
theorem first_eq_of_small_finite
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hmodel : SmallFiniteCarrier (K ⧸ pCore 2 K)) : f.Li 0 = K := by
  by_cases he : f.Li 0 = K
  · exact he
  have hn := small_finite_parameters hLK S.nonbinary hm hmodel
  have hXN : X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤
      normalizer (f.Vi 0 : Set G) := inf_le_left.trans (f.cartan_normalizes hu hX 0)
  have hcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 3 :=
    hXcard.trans (by rw [hn]; decide)
  rcases hmodel with h | h | h
  · exact (first_component_not_seven D S f hm hfix hK hLK hXN hcard hfaith (.inl h)).elim
  · exact (first_component_not_seven D S f hm hfix hK hLK hXN hcard hfaith (.inr h)).elim
  · exact (first_component_not_janko D S f hm hn hNT hK (lt_of_le_of_ne hLK he) h).elim

/-- The source refinement consumer has no exhaustive embedding-list premise. -/
theorem first_refinement_of_small_finite
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hmodel : SmallFiniteCarrier (K ⧸ pCore 2 K)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree := by
  have he := first_eq_of_small_finite D S f hu hm hfix hNT hX hK hLK hXcard hfaith hmodel
  exact .equal (by simpa using he)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
