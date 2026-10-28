module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.AlternativesData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.FourCentralizers

/-!
# Intermediate subgroups in the exceptional order-27 argument

These definitions retain the literal subgroups in Bender, *Finite groups
with large subgroups* (1974), proof of (4.1), printed p.225. The relative
normalizer is represented in the ambient group by intersection.

The two records below specify the local calculations still needed from
the exceptional normalizer. They assert neither the existence of the
conjugate centralizer nor a normal Sylow subgroup of its normalizer.
Their producers and the conjugate-centralizer and Sylow-normality steps
must all be proved before the exceptional configuration is excluded.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

/-- The subgroup denoted `Y = C_A(X)X` by Bender. -/
@[expose] public def exceptionalPlane (A X : Subgroup G) : Subgroup G :=
  (A ⊓ centralizer (X : Set G)) ⊔ X

/-- The ambient image of the relative normalizer `N_{N_G(A)}(Y)`. -/
@[expose] public def exceptionalPlaneNormalizer (A X : Subgroup G) : Subgroup G :=
  normalizer (A : Set G) ⊓ normalizer (exceptionalPlane A X : Set G)

/-- The fixed-space and relative-normalizer calculations in `3³:A₄`.
This is an intermediate contract, not a source theorem. -/
public structure ExceptionalLocalGeometry (A X : Subgroup G) : Prop where
  outside : ¬ X ≤ A
  fixed_card : Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 3
  plane_card : Nat.card (exceptionalPlane A X) = 9
  normalizer_card : Nat.card (exceptionalPlaneNormalizer A X) = 27
  normalizer_nonabelian : ¬ IsMulCommutative (exceptionalPlaneNormalizer A X)

/-- The local normalizer calculation and its Sylow normalizer-condition
consequence. This contract must also be proved for conjugates of `A`. -/
public structure ExceptionalSylowControl (A : Subgroup G) : Prop where
  unique_abelian : ∀ (S : Sylow 3 G), A ≤ (S : Subgroup G) →
    ∀ (B : Subgroup G), B ≤ (S : Subgroup G) →
      IsMulCommutative B → Nat.card B = 27 → B = A
  normalizes_nonabelian : ∀ (D : Subgroup G), D ≤ normalizer (A : Set G) →
    Nat.card D = 27 → ¬ IsMulCommutative D → A ≤ normalizer (D : Set G)

end CFSG.Quasithin.Janko1CentralizerData
