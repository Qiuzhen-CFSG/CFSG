module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CubicSubgroup
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.QuasithinBasic

/-!
# Cubic rank of an even-degree symplectic Borel

The two diagonal parameters contain independent elements of order three
when the binary field degree is even. The resulting elementary subgroup
of order nine gives the rank bound, and Sylow conjugacy transports it to
the normalizer of any specified Sylow subgroup.

Source: Aschbacher--Smith 14.6.20, printed p.1037, with the Borel calculation
of 15.3.49, p.1144. The terminal component sieve applies this to the literal
image of M intersect K, whose three-rank is at most one.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
variable {F : Type*} [Field F] [Finite F]

/-- The actual Borel contains two independent cubic directions. -/
theorem two_le_borel_threeRank {n : ℕ} (hF : Nat.card F = 2 ^ n) (he : Even n) :
    2 ≤ primeRank 3 (borel (F := F)) := by
  obtain ⟨E,hE,hcard⟩ := exists_cubic_borel_subgroup hF he
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_card E hcard

/-- The bound holds for the literal normalizer of any chosen Sylow subgroup. -/
theorem two_le_normalizer_threeRank {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 ≤ n) (he : Even n) (P : Sylow 2 (Sp F)) :
    2 ≤ primeRank 3 (normalizer (P : Set (Sp F))) := by
  rw [primeRank_equiv 3 (sylowNormalizerEquiv hF hn P)]
  exact two_le_borel_threeRank hF he
end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
