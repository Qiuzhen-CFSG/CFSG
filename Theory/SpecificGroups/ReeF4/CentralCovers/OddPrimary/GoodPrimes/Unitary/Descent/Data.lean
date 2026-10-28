module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.SL3Pair
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.AlgebraicTwist

/-!
# The split A₂ × A₂ construction needed for full unitary descent

The remaining geometric input is a homomorphism from two actual SL₃ factors
to the root-generated algebraic F₄ carrier. Its kernel must lie in the
diagonal cubic center. A Weyl representative must intertwine the algebraic
Ree twist with the explicit two-factor action in `SL3Pair`.

These are construction obligations, with no existence instance. They involve
only the split factors; `Descent` proves unitary fixed membership, faithfulness,
Lang conjugation, and comparison with the literal finite Ree group from them.
In particular the record does not request an SU₃ centralizer identification,
a projective quotient, or an assumed equivalence with the Ree model.

Source: GLS3 Example 2.6.3 and Table 4.7.3A,
`refs/KGroup/GLS3/chapter2.tex` and `chapter4.tex`.
-/

@[expose] public section

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent
open ReeF4.CentralCovers.OddPrimary.Cyclotomic

/-- Construction contract for the two algebraic A₂ factors, before taking
fixed points. No inhabitant of this structure is asserted here. -/
structure SubsystemData (m : ℕ) (F : Type*) [Field F] [IsAlgClosed F] [CharP F 2] where
  map : SL3 F × SL3 F →* AlgebraicPoints F
  kernel : ∀ A B, map (A, B) = 1 → A = B ∧ A ∈ Subgroup.center (SL3 F)
  weyl : AlgebraicPoints F
  intertwines : ∀ x, weyl * (algebraicReeTwist m).onPoints (map x) * weyl⁻¹ =
    map (pairTwist m x)


end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent
