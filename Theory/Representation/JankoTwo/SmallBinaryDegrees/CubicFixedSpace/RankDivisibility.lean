module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The remaining power-conjugation rank lemma

For an odd prime p, conjugacy of x to x² permutes its nonidentity eigenvalues
in orbits of length the multiplicative order of 2 modulo p. Thus the rank
of ρ(x)−1 is divisible by that order. The cubic and septic instances give
divisibility by two and three. This module specifies that general linear
algebra statement; it does not assert a proof of either instance.

The actual J₂ consumer uses checked power conjugators and Scott's inequality,
without assuming any catalogue of small modules. Source application:
Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1, p.16.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace
universe u v

/-- Rank divisibility from power conjugation, independently of J₂ or an
irreducible degree. A proof of the instances (3,2) and (7,3) is still needed. -/
@[expose] def PowerConjugacyRankDivisibility (p d : ℕ) : Prop :=
  ∀ (K : Type v) [Field K] [CharP K 2]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (G : Type u) [Group G] (ρ : Representation K G V) (x : G),
    x ^ p = 1 → (∃ g, g * x * g⁻¹ = x ^ 2) →
      d ∣ Module.finrank K (LinearMap.range (ρ x - 1))

end Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace
