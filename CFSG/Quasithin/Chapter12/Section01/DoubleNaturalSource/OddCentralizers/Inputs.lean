module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ModelGeometry

/-!
# Separate source inputs to the odd-centralizer argument

The three inputs below separate the ambient 4.4 normalizer theorem, the
E.3/E.2 construction inside an escaping centralizer, and the finite doubled
action calculations. None asserts a generation parameter or an r-bound.
They retain actual ambient actors and their literal fixed subspaces.

Source: Aschbacher--Smith, 12.1.9, printed pp.793--794.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G]

/-- Source 12.1.9(1), to be supplied by the actual 4.4 argument. -/
def OddNormalizerControl (W M : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≠ ⊥ → Odd (Nat.card X) → X ≤ M →
    X ≤ centralizer (W : Set G) → normalizer (X : Set G) ≤ M

/-- The E.3/E.2 output before applying odd-normalizer control or module geometry.
The actor fixes U and has a genuinely escaping full normalizer. -/
def EscapingOddActors (W M : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U ≤ W → ¬ centralizer (U : Set G) ≤ M →
    ∃ X : Subgroup G, X ≠ ⊥ ∧ Odd (Nat.card X) ∧ X ≤ M ∧
      X ≤ centralizer (U : Set G) ∧ ¬ normalizer (X : Set G) ≤ M

namespace DoubledBranch
variable {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- The finite odd-action calculation on n ⊕ n*, for an actual subgroup of M. -/
def OddActionGeometry : Prop :=
  ∀ X : Subgroup G, Odd (Nat.card X) → X ≤ normalizer (L : Set G) →
    ¬ X ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G) →
    (B.quadratic.comp (B.fixedSpace X).subtype).polarBilin.Nondegenerate ∧
      4 ≤ finrank (ZMod 2) ((Additive (componentOrbit V (T : Subgroup G))) ⧸ B.fixedSpace X)

end DoubledBranch

/-- The other finite action calculation in 12.1.9: odd-primary subgroups
permuting with the actual full Sylow act trivially when their prime exceeds 3. -/
def LargePrimeSylowAction (W M : Subgroup G) (T : Sylow 2 G) : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ X : Subgroup G, IsPGroup p X → X ≤ M →
    (X : Set G) * (T : Set G) = (T : Set G) * (X : Set G) →
    X ≤ centralizer (W : Set G)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
