module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SmallSporadic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstSporadic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.TripleMathieu
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstFieldFour

/-!
# First-normalizer refinement for M₂₂, 3.M₂₂, M₂₃ and HS

The actual smaller PSL₂ section forces field four in each carrier. Thus the
literal Cartan centralizer has order three and remains faithful on V₁.
The proved cubic exclusions eliminate the three centerless carriers, and
the existing exponent-three Sylow argument eliminates the triple Mathieu
cover. The first-index refinement uses no exhaustive embedding-list or
field-degree premise.

The preceding quotient marking, Cartan action and L₁-centralization belong
to qt-d-1222-natural-flag-cartan, with final discharge by
qt-d-1222-natural-local-geometry. The relative-components owner retains
the other carriers and the field-four triangle.
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

/-- The four small sporadic carriers are excluded at the first normalizer,
with the field-four parameter derived from the literal smaller section. -/
theorem first_not_small_sporadic
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ¬ SmallSporadicCarrier (K ⧸ pCore 2 K) := by
  intro hmodel
  let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  have hn := small_sporadic_parameters hLK S.nonbinary hm hmodel
  have hXN : X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤
      normalizer (f.Vi 0 : Set G) := inf_le_left.trans (f.cartan_normalizes hu hX 0)
  have hcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 3 :=
    hXcard.trans (by rw [hn]; decide)
  have he := first_component_not_cubic_sporadic D S f hm hfix hK hLK hXN hcard hfaith
  rcases hmodel with h | h | h | h
  · exact he (FirstCubicSporadic.of_small_carrier (A := K ⧸ pCore 2 K) (.inl h))
  · exact first_component_not_mathieu_cover D S f hm hfix hK hLK hXN hcard hfaith h
  · exact he (FirstCubicSporadic.of_small_carrier (A := K ⧸ pCore 2 K) (.inr (.inl h)))
  · exact he (FirstCubicSporadic.of_small_carrier (A := K ⧸ pCore 2 K) (.inr (.inr h)))

/-- The actual first refinement in these carrier rows uses no exhaustive
embedding-list premise. -/
theorem first_refinement_of_small_sporadic
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hmodel : SmallSporadicCarrier (K ⧸ pCore 2 K)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree :=
  (first_not_small_sporadic D S f hu hm hfix hX hK hLK hXcard hfaith hmodel).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
