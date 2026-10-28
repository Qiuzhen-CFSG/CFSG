module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstSporadic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.TripleMathieu
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Normalization
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry

/-!
# The field-four first-normalizer sieve with the literal Cartan factor

The cubic arguments exclude A₇, its three-cover, M₂₂, its three-cover,
M₂₃, J₂, J₄, HS and Ru. The odd-kernel rows already give the exact
SL₂ two-odd-quotient refinement. This leaves just the prime-field PSL₂,
PSL₂(25), signed degree-three field-five and J₁ rows for further analysis.

The source consumer uses X₁ = C_X(L₁/O₂(L₁)), defined by the actual
normalizer action. Inner-Sylow flag uniqueness supplies its normalization;
the source cardinality q−1 and faithful action on V₁ give the cubic actor.
The earlier flag/Cartan owner supplies those two geometric facts, and
qt-d-1222-natural-local-geometry owns their ultimate discharge. This task
retains the four remaining rows, characteristic-two rows, triangle and
full 11.1.1–11.1.3 assembly. The reduced disjunction is not full 11.1.2.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.1(3) and 11.1.2, printed pp.761–762.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Nine model exclusions and the two odd-extension refinements leave four
explicit field-four model rows. The larger embedding list remains a premise. -/
theorem first_fieldFour_refinement_or_four_rows
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G)) (hXcard : Nat.card X₁ = 3)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hfour : S.field.degree = 2) (hk : FieldFourOvergroup (K ⧸ pCore 2 K)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      (∃ p, Source.ExceptionalPrime p ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 ∨
      (∃ u, IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨ IsSLSign (K ⧸ pCore 2 K) u 3 5) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  rcases first_fieldFour_cubic_sieve D S f hm hfix hK hLK hXN hXcard hfaith hfour hk
    with h | h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr h)))
  · exact (first_component_not_mathieu_cover D S f hm hfix hK hLK hXN hXcard hfaith h).elim

/-- Apply the proved field-four sieve to X₁ = C_X(L₁/O₂(L₁)), with the
source Hall Cartan and the original flag. Its normalization is discharged. -/
theorem first_fieldFour_refinement_or_four_rows_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hfour : S.field.degree = 2) (hk : FieldFourOvergroup (K ⧸ pCore 2 K)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      (∃ p, Source.ExceptionalPrime p ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 ∨
      (∃ u, IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨ IsSLSign (K ⧸ pCore 2 K) u 3 5) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  exact first_fieldFour_refinement_or_four_rows D S f hm hfix hK hLK
    (inf_le_left.trans (f.cartan_normalizes hu hX 0))
    (hXcard.trans (by rw [hfour]; decide)) hfaith hfour hk

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
