module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalInput
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.CartanRank

/-!
# The Cartan prime exclusion on the literal chosen quotient

A nonzero subspace of the chosen fixed-space quotient pulls back to a
nontrivial elementary abelian subgroup in the original V. Its normalizer is
therefore an actual two-local. The Cartan rank-two argument applies inside
that normalizer and excludes every prime dividing q - 1 from the order of
the disjoint normalized subgroup Y.

This supplies the numerical step of 11.5.6(1) for the Chapter 12 choice.
The geometric construction of X and Y and the remaining 11.5 arguments
are separate source obligations; this is not the exclusion theorem 11.0.1.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.5.6(1) and the use of 11.0.1 in 12.2.2, printed pp.780,795.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- On the actual quotient preimage, the source local-rank argument excludes
all primes dividing q - 1. Only the displayed geometric inputs remain. -/
theorem centralQuotientPreimage_cartan_coprime_of_many
    (S : D.NonbinaryNaturalInput)
    (U : Submodule (ZMod 2) D.chosenCentralQuotient) (hU : U ≠ ⊥)
    (X Y : Subgroup G)
    (hX : X ≤ normalizer (D.centralQuotientPreimage U : Set G))
    (hY : Y ≤ normalizer (D.centralQuotientPreimage U : Set G))
    (hr : ∀ p : ℕ, p.Prime → p ∣ 2 ^ S.field.degree - 1 → 2 ≤ primeRank p X)
    (hn : X ≤ normalizer (Y : Set G)) (hd : Disjoint X Y) :
    Nat.Coprime (Nat.card Y) (2 ^ S.field.degree - 1) := by
  have he : Even (2 ^ S.field.degree) :=
    (show Even (2 : ℕ) from ⟨1, rfl⟩).pow_of_ne_zero (Nat.ne_of_gt S.field.degree_pos)
  have hpos : 0 < (2 : ℕ) ^ S.field.degree := pow_pos (by decide) _
  have hodd : Odd (2 ^ S.field.degree - 1) :=
    (Nat.odd_sub' hpos).mpr (by simpa using he)
  exact Chapter11.ChosenNaturalSource.cartan_coprime_field_predecessor
    S.source.simpleQTKE.quasithin _ X Y
    (D.centralQuotientPreimage_twoLocal U hU) hX hY hodd hr hn hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
